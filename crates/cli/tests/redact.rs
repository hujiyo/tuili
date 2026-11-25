//! End-to-end tests for display-layer redaction (`--redact` / `:redact`).
//!
//! Redaction rewrites printed individual names to stable placeholders and never
//! touches a derivation, an exit code or the certificate content: the exported
//! certificate keeps the case text (so `:verify-cert` can re-check it) and a
//! redacted session must still pass that verification.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;

const REDACT_NOTICE: &str = "输出已脱敏；证书未脱敏。";
const DEFAULT_NOTICE: &str = "显示层脱敏：已关闭。";

/// A theory whose case text mentions the individuals in a fact label, a source
/// and a rule name, so redaction must rewrite more than bare propositions.
const CASE: &str = "sort 人\n\
                    pred 殴打他人 : 人 → 人 → Prop\n\
                    pred 人身受到伤害 : 人 → Prop\n\
                    obj 张三 : 人\n\
                    obj 李四 : 人\n\
                    axiom 张三殴打李四 : 殴打他人 张三 李四\n\
                    \x20 source text \"案情记录：张三殴打李四\" locator \"第一页\"\n\
                    rule 张三殴打李四致其受伤 :\n\
                    \x20 params a : 人, b : 人\n\
                    \x20 premise 殴打他人 a b\n\
                    \x20 conclude 人身受到伤害 b\n\
                    \x20 source text \"刑法\" locator \"第二百三十四条\"\n";

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-redact-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn write(&self, name: &str, text: &str) -> String {
        let path = self.path.join(name);
        fs::write(&path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path.display().to_string()
    }

    fn path(&self, name: &str) -> PathBuf {
        self.path.join(name)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(commands: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(commands)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn session(file: &str, options: &[&str], commands: &[&str]) -> Output {
    let mut all = vec!["--no-default-packs".to_owned()];
    all.extend(options.iter().map(|option| (*option).to_owned()));
    all.push(file.to_owned());
    all.extend(commands.iter().map(|command| (*command).to_owned()));
    run(&all)
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

fn case_file(dir: &TempDir) -> String {
    dir.write("case.std", CASE)
}

/// The derivation part of a `:why` output: everything from the first `▸` line.
fn derivation(out: &str) -> &str {
    let start = out
        .find("▸ ")
        .unwrap_or_else(|| panic!("no derivation line:\n{out}"));
    &out[start..]
}

#[test]
fn redacted_why_contains_no_original_name_and_stable_placeholders() {
    let dir = TempDir::new("why");
    let file = case_file(&dir);
    let output = session(&file, &["--redact"], &[":why 人身受到伤害 李四"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(!out.contains("张三"), "the original name leaked:\n{out}");
    assert!(!out.contains("李四"), "the original name leaked:\n{out}");
    assert!(
        out.contains("甲1"),
        "the first placeholder must appear:\n{out}"
    );
    assert!(
        out.contains("甲2"),
        "the second placeholder must appear:\n{out}"
    );
    // The mapping is the declared-name order: 张三 sorts before 李四.
    let tree = derivation(&out);
    assert!(
        tree.contains("人身受到伤害 甲2"),
        "the conclusion uses the case's second individual:\n{tree}"
    );
    assert!(
        tree.contains("殴打他人 甲1 甲2"),
        "the premise uses both placeholders:\n{tree}"
    );
    assert!(out.contains(REDACT_NOTICE), "{out}");
    assert!(
        out.contains("声明：这是模型内推导，不是法律意见。"),
        "{out}"
    );

    let second = session(&file, &["--redact"], &[":why 人身受到伤害 李四"]);
    assert_eq!(
        stdout(&output),
        stdout(&second),
        "two redacted runs must be byte-identical"
    );
}

#[test]
fn redaction_rewrites_sources_labels_and_rule_names_too() {
    let dir = TempDir::new("sources");
    let file = case_file(&dir);
    let output = session(&file, &["--redact"], &[":why 人身受到伤害 李四"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("案情记录：甲1殴打甲2"),
        "the source text must be redacted as well\n{out}"
    );
    assert!(
        out.contains("[甲1殴打甲2]"),
        "the fact label must be redacted as well\n{out}"
    );
    assert!(
        out.contains("⟨甲1殴打甲2致其受伤⟩"),
        "the rule name must be redacted as well\n{out}"
    );
    for line in out.lines() {
        assert!(
            !line.contains("张三") && !line.contains("李四"),
            "leaked name on line {line:?}"
        );
    }
}

#[test]
fn every_redacted_query_command_uses_the_same_mapping() {
    let dir = TempDir::new("stable");
    let file = case_file(&dir);
    for command in ["why", "explain", "labels"] {
        let output = session(
            &file,
            &["--redact"],
            &[&format!(":{command} 人身受到伤害 李四")],
        );
        assert_exit(&output, PROVED);
        let out = stdout(&output);
        assert!(!out.contains("张三") && !out.contains("李四"), "{out}");
        assert!(
            out.contains("甲1"),
            "`{command}` must use the same placeholders\n{out}"
        );
        assert!(
            out.contains("甲2"),
            "`{command}` must use the same placeholders\n{out}"
        );
        assert!(out.contains(REDACT_NOTICE), "{out}");
    }
}

#[test]
fn the_certificate_keeps_the_case_text_and_still_verifies() {
    let dir = TempDir::new("cert");
    let file = case_file(&dir);
    let output = session(&file, &["--redact"], &[":cert 人身受到伤害 李四"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("证书包含案件原文，可能含个人信息，分享前请自行处理"),
        "{out}"
    );
    let start = out
        .find('{')
        .expect("the certificate JSON follows the notice");
    let json = &out[start..];
    assert!(
        json.contains("张三") && json.contains("李四"),
        "the certificate must keep the original names:\n{json}"
    );
    assert!(
        !json.contains("甲1"),
        "the certificate must not be redacted:\n{json}"
    );
    let cert = dir.path("cert.json");
    fs::write(&cert, json.as_bytes()).expect("write the certificate");
    let verify = session(
        &file,
        &["--redact"],
        &[&format!(":verify-cert {}", cert.display())],
    );
    assert_exit(&verify, PROVED);
    let report = stdout(&verify);
    assert!(report.contains("逻辑校验：通过"), "{report}");
    assert!(report.contains("内核证明：通过"), "{report}");
}

#[test]
fn redaction_can_be_switched_off_and_then_the_default_output_returns() {
    let dir = TempDir::new("switch");
    let file = case_file(&dir);
    let plain = session(&file, &[], &[":why 人身受到伤害 李四"]);
    assert_exit(&plain, PROVED);
    let plain_out = stdout(&plain);

    let switched = session(&file, &["--redact"], &[":redact", ":why 人身受到伤害 李四"]);
    // `:redact` with no argument only reports the state, so the derivation after
    // `:redact off` below is the unredacted one.
    assert!(
        stdout(&switched).contains("显示层脱敏：已开启"),
        "{:?}",
        stdout(&switched)
    );

    let off = session(
        &file,
        &["--redact"],
        &[":redact off", ":why 人身受到伤害 李四"],
    );
    assert_exit(&off, PROVED);
    let off_out = stdout(&off);
    assert!(off_out.contains(DEFAULT_NOTICE), "{off_out}");
    assert!(
        derivation(&off_out) == derivation(&plain_out),
        "with redaction off the derivation is byte-identical to the default:\n--- default ---\n{plain_out}\n--- off ---\n{off_out}"
    );
    assert!(
        off_out.contains("张三") && off_out.contains("李四"),
        "{off_out}"
    );
}

#[test]
fn the_redaction_notice_is_printed_with_every_redacted_output() {
    let dir = TempDir::new("notice");
    let file = case_file(&dir);
    for command in ["why", "explain", "labels"] {
        let output = session(
            &file,
            &["--redact"],
            &[&format!(":{command} 人身受到伤害 李四")],
        );
        let out = stdout(&output);
        // The batch entry prints the (redacted) load report first, then the
        // command; each redacted block ends with the same notice.
        assert_eq!(
            out.matches(REDACT_NOTICE).count(),
            2,
            "the load report and `:{command}` must each state the display boundary once\n{out}"
        );
        assert!(
            out.contains("证书未脱敏"),
            "`:{command}` must say the certificate was not redacted\n{out}"
        );
    }
}

#[test]
fn an_unknown_redact_argument_is_a_command_error() {
    let dir = TempDir::new("arg");
    let file = case_file(&dir);
    let output = session(&file, &[], &[":redact 有时"]);
    assert_exit(&output, 2);
    let err = stderr(&output);
    assert!(err.contains("用法：:redact"), "{err}");
}

#[test]
fn inspect_is_redacted_too_and_shows_the_placeholder_object() {
    let dir = TempDir::new("inspect");
    let file = case_file(&dir);
    let output = session(&file, &["--redact"], &[":inspect"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(!out.contains("张三") && !out.contains("李四"), "{out}");
    assert!(out.contains("obj   甲1 : 人"), "{out}");
    assert!(out.contains("obj   甲2 : 人"), "{out}");
}
