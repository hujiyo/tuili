//! The declaration layer for burden of proof and standards of proof, end to
//! end: `:inspect` shows what was declared (and only what was declared), and
//! declaring anything changes neither the derivation nor the certificate.
//!
//! The reasoning/certificate comparison is byte for byte on purpose: these
//! fields are declarations for a later report, not premises of the calculus.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const COMMAND_ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Run the CLI from the repository root. `--no-default-packs` keeps the
/// session to the file under test: no registry, no profile, no official pack.
fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .arg("--no-default-packs")
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

/// A theory file outside the repository, removed when the test ends.
struct TempTheory {
    path: PathBuf,
}

impl TempTheory {
    fn new(tag: &str, source: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-burden-{}-{tag}-{n}.std",
            std::process::id()
        ));
        fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempTheory { path }
    }
}

impl Drop for TempTheory {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn load_and(theory: &TempTheory, command: &str) -> Output {
    run(&[
        format!(":load {}", theory.path.display()),
        command.to_owned(),
    ])
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

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

/// The line `:inspect` prints for the rule called `name`.
fn rule_line(out: &str, name: &str) -> String {
    let prefix = format!("rule  {name} :");
    out.lines()
        .find(|line| line.contains(&prefix))
        .unwrap_or_else(|| panic!("no `:inspect` line for rule {name}:\n{out}"))
        .to_owned()
}

const INSPECT_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 免责 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "事实"

rule 有声明 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  burden claimant
  standard preponderance
  exception_burden respondent
  exception_standard clear_and_convincing
  source text "测试" locator "一"

rule 只有标准 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  standard beyond_reasonable_doubt
  source text "测试" locator "二"

rule 只有例外举证 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  exception_burden court
  source text "测试" locator "三"

rule 只有例外标准 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  exception_standard preponderance
  source text "测试" locator "四"

rule 未声明 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  source text "测试" locator "五"
"#;

#[test]
fn inspect_shows_burden_and_standard_declarations() {
    let theory = TempTheory::new("inspect", INSPECT_THEORY);
    let output = check(load_and(&theory, ":inspect"), PROVED, &["已加载"]);
    let out = stdout(&output);

    let declared = rule_line(&out, "有声明");
    assert!(
        declared.contains("〔举证 claimant · 标准 preponderance〕"),
        "the burden/standard group is missing: {declared}"
    );
    assert!(
        declared.contains("〔例外举证 respondent · 例外标准 clear_and_convincing〕"),
        "the exception group is missing: {declared}"
    );

    let standard_only = rule_line(&out, "只有标准");
    assert!(
        standard_only.contains("〔标准 beyond_reasonable_doubt〕"),
        "an undeclared burden must not be shown, nor replaced by a default: {standard_only}"
    );
    assert!(
        !standard_only.contains("举证"),
        "no burden was declared, so no `举证` may be printed: {standard_only}"
    );

    let exception_only = rule_line(&out, "只有例外举证");
    assert!(
        exception_only.contains("〔例外举证 court〕"),
        "the exception burden is missing: {exception_only}"
    );
    assert!(
        !exception_only.contains("例外标准") && !exception_only.contains("〔举证"),
        "only the declared exception field may be shown: {exception_only}"
    );

    let exception_standard_only = rule_line(&out, "只有例外标准");
    assert!(
        exception_standard_only.contains("〔例外标准 preponderance〕"),
        "the exception standard is missing: {exception_standard_only}"
    );
    assert!(
        !exception_standard_only.contains("例外举证")
            && !exception_standard_only.contains("〔举证")
            && !exception_standard_only.contains("〔标准"),
        "only the declared exception field may be shown: {exception_standard_only}"
    );

    let undeclared = rule_line(&out, "未声明");
    for marker in [
        "〔举证",
        "〔标准",
        "〔例外举证",
        "〔例外标准",
        "claimant",
        "preponderance",
    ] {
        assert!(
            !undeclared.contains(marker),
            "an undeclared rule must print no breakdown ({marker}): {undeclared}"
        );
    }
}

const BASE_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 免责 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "事实"
rule 规则 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  source text "测试" locator "一"
"#;

const DECLARED_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 免责 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "事实"
rule 规则 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 免责 p
  burden claimant
  standard clear_and_convincing
  exception_burden respondent
  exception_standard beyond_reasonable_doubt
  source text "测试" locator "一"
"#;

/// The derivation section of `:why`, starting at the root line.
fn why_section(output: &Output) -> String {
    let out = stdout(output);
    let start = out
        .find('▸')
        .unwrap_or_else(|| panic!("no derivation in the output:\n{out}"));
    out[start..].to_owned()
}

/// The certificate JSON, starting at its first `{`.
fn cert_section(output: &Output) -> String {
    let out = stdout(output);
    let start = out
        .find('{')
        .unwrap_or_else(|| panic!("no certificate in the output:\n{out}"));
    out[start..].to_owned()
}

#[test]
fn declaring_burden_and_standard_does_not_change_the_derivation() {
    let base = TempTheory::new("why-base", BASE_THEORY);
    let declared = TempTheory::new("why-declared", DECLARED_THEORY);
    let base_out = check(
        load_and(&base, ":why 违法 张三"),
        PROVED,
        &["推导已通过独立校验。"],
    );
    let declared_out = check(
        load_and(&declared, ":why 违法 张三"),
        PROVED,
        &["推导已通过独立校验。"],
    );
    assert_eq!(
        why_section(&base_out),
        why_section(&declared_out),
        "burden/standard declarations must not change the derivation"
    );
}

#[test]
fn declaring_burden_and_standard_does_not_change_the_certificate() {
    let base = TempTheory::new("cert-base", BASE_THEORY);
    let declared = TempTheory::new("cert-declared", DECLARED_THEORY);
    let base_out = check(
        load_and(&base, ":cert 违法 张三"),
        PROVED,
        &["\"format_version\": 6"],
    );
    let declared_out = check(
        load_and(&declared, ":cert 违法 张三"),
        PROVED,
        &["\"format_version\": 6"],
    );
    assert_eq!(
        cert_section(&base_out),
        cert_section(&declared_out),
        "burden/standard declarations must not change the certificate"
    );
}

const ILLEGAL_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "事实"
rule 规则 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  burden plaintiff
  source text "测试" locator "一"
"#;

#[test]
fn an_illegal_value_fails_the_load_with_rule_field_and_allowed_values() {
    let theory = TempTheory::new("illegal", ILLEGAL_THEORY);
    let output = load_and(&theory, ":quit");
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(code, Some(COMMAND_ERROR), "stdout:\n{out}\nstderr:\n{err}");
    assert!(
        err.contains("错误："),
        "the `:load` error keeps its prefix: {err}"
    );
    for needle in [
        "error: 规则 `规则` 的 burden 取值 `plaintiff` 非法",
        "claimant",
        "respondent",
        "court",
    ] {
        assert!(
            err.contains(needle),
            "the diagnostic must contain {needle:?}:\n{err}"
        );
    }
}
