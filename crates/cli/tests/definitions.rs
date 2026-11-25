//! End-to-end tests for `def` as a named macro.
//!
//! A definition is not a second macro system: the kernel already unfolds a
//! `def` by delta during conversion, so one name can stand in a fact type, a
//! premise, a conclusion and an `unless`. These tests pin the user-visible
//! contract: one definition serves several rules, `:inspect` shows what the
//! name expands to, a changed body changes the derivation, recursion and
//! unbound names are refused at load, and the certificate layers still check
//! a derivation whose premises use a definition.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP: i32 = 1;
const COMMAND_ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(arguments: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(arguments)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn next_suffix() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    NEXT.fetch_add(1, Ordering::Relaxed)
}

/// A theory file outside the repository, removed when the test ends.
struct TempTheory {
    path: PathBuf,
}

impl TempTheory {
    fn new(tag: &str, source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "std-deduce-definitions-{}-{tag}-{}.std",
            std::process::id(),
            next_suffix()
        ));
        fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempTheory { path }
    }

    fn path_str(&self) -> String {
        self.path.display().to_string()
    }

    /// Run the CLI on this theory alone: the default legal environment must
    /// not add rules that could explain a derivation instead of the definition.
    fn session(&self, commands: &[&str]) -> Output {
        let mut all = vec![
            "--no-default-packs".to_string(),
            format!(":load {}", self.path.display()),
        ];
        all.extend(commands.iter().map(|command| command.to_string()));
        run(all)
    }
}

impl Drop for TempTheory {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn check(output: Output, expected: i32, needles: &[&str]) {
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
}

/// One definition of `夫妻` is written once and used by two rules. Both rules
/// load and both derive their own conclusion; the inspect ledger keeps the
/// name as a `def` (not as two expanded copies).
const TWO_RULES: &str = r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 殴打 : 人 → 人 → Prop
pred 须保护 : 人 → 人 → Prop
pred 须回避 : 人 → 人 → Prop

obj 张三 : 人
obj 李四 : 人

def 夫妻 : 人 → 人 → Prop := λ (a : 人) := λ (b : 人) := 配偶 a b

axiom 夫妻事实 : 夫妻 张三 李四
  source text "测试" locator "夫妻"
axiom 殴打事实 : 殴打 李四 张三
  source text "测试" locator "殴打"

rule 夫妻互殴须保护 :
  params a : 人, b : 人
  premise 夫妻 a b
  premise 殴打 b a
  conclude 须保护 a b
  source text "测试" locator "规则一"

rule 夫妻互殴须回避 :
  params a : 人, b : 人
  premise 殴打 b a
  premise 夫妻 a b
  conclude 须回避 a b
  source text "测试" locator "规则二"

#show 夫妻
"#;

#[test]
fn one_definition_serves_two_rules_and_both_derive() {
    let theory = TempTheory::new("two-rules", TWO_RULES);
    let output = theory.session(&[":why 须保护 张三 李四", ":why 须回避 张三 李四"]);
    check(
        output,
        PROVED,
        &[
            "⟨夫妻互殴须保护⟩",
            "⟨夫妻互殴须回避⟩",
            "· 夫妻 张三 李四",
            "推导已通过独立校验。",
        ],
    );
}

/// `:inspect` shows a definition as name → type → body, with the λ binder
/// order visible. The expansion is auditable rather than hidden in the
/// kernel's delta rule; `#show` prints the body too.
#[test]
fn inspect_and_show_expose_the_expansion() {
    let theory = TempTheory::new("inspect", TWO_RULES);
    let output = theory.session(&[":inspect"]);
    let out = stdout(&output);
    check(
        output,
        PROVED,
        &[
            "def   夫妻 : 人 → 人 → Prop",
            ":= λ (a : 人), λ (b : 人), 配偶 a b",
        ],
    );
    let def_line = out
        .lines()
        .position(|line| line.starts_with("  def   夫妻 : 人"))
        .unwrap_or_else(|| panic!("no def line in `:inspect`:\n{out}"));
    let body_line = out
        .lines()
        .position(|line| line.starts_with("       := λ (a : 人), λ (b : 人), 配偶 a b"))
        .unwrap_or_else(|| panic!("no expansion line in `:inspect`:\n{out}"));
    assert_eq!(
        body_line,
        def_line + 1,
        "the expansion must sit directly under its declaration:\n{out}"
    );
    // The load report's `#show` line carries the body as well.
    let load = theory.session(&[]);
    check(
        load,
        PROVED,
        &["· 夫妻 : 人 → 人 → Prop := λ (a : 人), λ (b : 人), 配偶 a b"],
    );
}

/// The same rules and facts with only the definition body edited: the rule's
/// conclusion is the name `夫妻`, so the body decides which `配偶` instance
/// reaches the fact base. Nothing is baked into the rule at load time.
fn definition_body(head: &str) -> String {
    format!(
        r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 殴打 : 人 → 人 → Prop

obj 张三 : 人
obj 李四 : 人

def 夫妻 : 人 → 人 → Prop := λ (a : 人) := λ (b : 人) := {head}

axiom 殴打事实 : 殴打 李四 张三
  source text "测试" locator "殴打"

rule 夫妻互殴 :
  params a : 人, b : 人
  premise 殴打 b a
  conclude 夫妻 a b
  source text "测试" locator "规则"
"#
    )
}

#[test]
fn a_changed_definition_body_changes_behaviour() {
    let good = TempTheory::new("body-good", &definition_body("配偶 a b"));
    check(
        good.session(&[":why 配偶 张三 李四"]),
        PROVED,
        &["▸ 夫妻 张三 李四", "⟨夫妻互殴⟩", "推导已通过独立校验。"],
    );
    check(
        good.session(&[":why 配偶 李四 张三"]),
        GAP,
        &["【未闭合】", "缺：殴打 张三 李四"],
    );

    // Only the body changed: `夫妻 a b` now means `配偶 b a`, so the two
    // queries swap their answers. If the old body had been cached, neither
    // flip would happen.
    let swapped = TempTheory::new("body-swapped", &definition_body("配偶 b a"));
    check(
        swapped.session(&[":why 配偶 李四 张三"]),
        PROVED,
        &["▸ 夫妻 张三 李四", "⟨夫妻互殴⟩", "推导已通过独立校验。"],
    );
    check(
        swapped.session(&[":why 配偶 张三 李四"]),
        GAP,
        &["【未闭合】", "缺：殴打 张三 李四"],
    );
}

/// A definition also stands in an `unless` and in a fact's type: the fact
/// records the written name, and the blocker is matched through delta,
/// reporting the user-written name.
const UNLESS_AND_FACT_TYPE: &str = r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 殴打 : 人 → 人 → Prop
pred 须保护 : 人 → 人 → Prop

obj 张三 : 人
obj 李四 : 人

def 夫妻 : 人 → 人 → Prop := λ (a : 人) := λ (b : 人) := 配偶 a b
def 互殴 : 人 → 人 → Prop := λ (a : 人) := λ (b : 人) := 殴打 b a

axiom 夫妻事实 : 夫妻 张三 李四
  source text "测试" locator "夫妻"
axiom 殴打事实 : 殴打 李四 张三
  source text "测试" locator "殴打"

rule 夫妻互殴须保护 :
  params a : 人, b : 人
  premise 互殴 a b
  unless 夫妻 a b
  conclude 须保护 a b
  source text "测试" locator "规则"
"#;

#[test]
fn definitions_are_honoured_in_unless_and_in_fact_types() {
    let theory = TempTheory::new("unless", UNLESS_AND_FACT_TYPE);
    // The fact's ledger entry keeps the written definition name.
    check(
        theory.session(&[":inspect"]),
        PROVED,
        &["fact  夫妻事实 : 夫妻 张三 李四"],
    );
    // The `unless` is a def application; its blocker holds only because the
    // kernel unfolds it to the `配偶` fact. The report names the written form.
    check(
        theory.session(&[":why 须保护 张三 李四"]),
        GAP,
        &["被阻断：「夫妻 张三 李四」", "已成立"],
    );
}

/// Renaming a definition renames the reference in every rule; the old name is
/// unknown, not silently resolved to the new macro.
const RENAMED: &str = r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 须保护 : 人 → 人 → Prop
obj 张三 : 人
obj 李四 : 人
def 伴侣 : 人 → 人 → Prop := λ (a : 人) := λ (b : 人) := 配偶 a b
axiom 伴侣事实 : 伴侣 张三 李四
  source text "测试" locator "伴侣"
rule 伴侣须保护 :
  params a : 人, b : 人
  premise 伴侣 a b
  conclude 须保护 a b
  source text "测试" locator "规则"
"#;

#[test]
fn a_renamed_definition_is_used_by_its_new_name_only() {
    let theory = TempTheory::new("renamed", RENAMED);
    check(
        theory.session(&[":why 须保护 张三 李四"]),
        PROVED,
        &["⟨伴侣须保护⟩", "推导已通过独立校验。"],
    );
    let old = theory.session(&[":why 夫妻 张三 李四"]);
    assert_eq!(old.status.code(), Some(COMMAND_ERROR), "{}", stderr(&old));
    assert!(stderr(&old).contains("未知名称"), "{}", stderr(&old));
}

/// Invalid definitions are refused at load with the declaration's own
/// position and name: recursion, an unbound free name, a name clash and a
/// body that does not match its declared type.
#[test]
fn invalid_definitions_are_refused_at_load_with_name_and_position() {
    let recursive = TempTheory::new(
        "recursive",
        "sort 人\npred 殴打 : 人 → Prop\ndef 循环 : 人 → Prop := λ (x : 人) := 循环 x\n",
    );
    let output = recursive.session(&[]);
    assert_eq!(
        output.status.code(),
        Some(COMMAND_ERROR),
        "{}",
        stderr(&output)
    );
    let err = stderr(&output);
    assert!(err.contains(":3:1"), "{err}");
    assert!(err.contains("`def 循环`"), "{err}");
    assert!(err.contains("定义不能递归"), "{err}");

    let unbound = TempTheory::new(
        "unbound",
        "sort 人\npred 殴打 : 人 → Prop\ndef 缺参 : 人 → Prop := λ (x : 人) := 殴打 y\n",
    );
    let output = unbound.session(&[]);
    assert_eq!(
        output.status.code(),
        Some(COMMAND_ERROR),
        "{}",
        stderr(&output)
    );
    let err = stderr(&output);
    assert!(err.contains(":3:1"), "{err}");
    assert!(err.contains("`def 缺参`") && err.contains("`y`"), "{err}");

    let clash = TempTheory::new(
        "clash",
        "sort 人\npred 殴打 : 人 → Prop\ndef 殴打 : 人 → Prop := λ (x : 人) := 殴打 x\n",
    );
    let output = clash.session(&[]);
    assert_eq!(
        output.status.code(),
        Some(COMMAND_ERROR),
        "{}",
        stderr(&output)
    );
    let err = stderr(&output);
    assert!(err.contains(":3:1"), "{err}");
    assert!(err.contains("`def 殴打`"), "{err}");
    assert!(err.contains("`pred`"), "{err}");

    let wrong_type = TempTheory::new(
        "wrong-type",
        "sort 人\npred 殴打 : 人 → Prop\ndef 坏 : 人 → Prop := λ (x : 人) := λ (y : 人) := 殴打 y\n",
    );
    let output = wrong_type.session(&[]);
    assert_eq!(
        output.status.code(),
        Some(COMMAND_ERROR),
        "{}",
        stderr(&output)
    );
    let err = stderr(&output);
    assert!(err.contains(":3:1"), "{err}");
    assert!(err.contains("`def 坏`"), "{err}");
    assert!(err.contains("类型不匹配"), "{err}");
}

/// A certificate over a derivation whose premises use a definition still
/// passes both `cert::check` and `cert::kernel_proof`; tampering with the
/// recorded kernel term still fails, so the macro does not widen the check.
#[test]
fn certificates_over_definitions_pass_both_layers_and_tampering_still_fails() {
    let theory = TempTheory::new("cert", TWO_RULES);
    let output = theory.session(&[":cert 须保护 张三 李四"]);
    assert_eq!(output.status.code(), Some(PROVED), "{}", stderr(&output));
    let text = stdout(&output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    let json = &text[start..];

    let cert = TempJson::new("good", json);
    let verify = run(vec![
        "--no-default-packs".to_string(),
        format!(":load {}", theory.path_str()),
        format!(":verify-cert {}", cert.path_str()),
    ]);
    check(verify, PROVED, &["逻辑校验：通过", "内核证明：通过"]);

    // The certificate records the kernel term as written: the assumption's
    // head is the `def` constant, and delta reduction happens in the kernel
    // when the two layers compare it with the rule's premise.
    assert!(
        json.contains("\"name\": \"夫妻\""),
        "the certificate must record the kernel term, not a pretty expansion:\n{json}"
    );

    // A definition must not widen the check: claiming a strict identity for
    // the assumption is still rejected against the environment registry.
    let mut value: serde_json::Value =
        serde_json::from_str(json).unwrap_or_else(|e| panic!("certificate JSON: {e}"));
    let assumptions = value["assumptions"]
        .as_array_mut()
        .unwrap_or_else(|| panic!("assumptions must be an array"));
    let target = assumptions
        .iter_mut()
        .find(|assumption| {
            assumption["proposition"]["kind"] == "app"
                && assumption["proposition"]["func"]["func"]["name"] == "夫妻"
        })
        .unwrap_or_else(|| panic!("no `夫妻` assumption in the certificate:\n{json}"));
    target["identity"] = serde_json::json!("verified");
    let tampered = TempJson::new(
        "tampered",
        &serde_json::to_string_pretty(&value).expect("re-serialize"),
    );
    let verify = run(vec![
        "--no-default-packs".to_string(),
        format!(":load {}", theory.path_str()),
        format!(":verify-cert {}", tampered.path_str()),
    ]);
    let code = verify.status.code();
    let out = stdout(&verify);
    let err = stderr(&verify);
    assert_eq!(code, Some(COMMAND_ERROR), "stdout:\n{out}\nstderr:\n{err}");
    assert!(out.contains("逻辑校验：失败"), "{out}");
    assert!(err.contains("证书校验失败"), "{err}");
}

/// A JSON file removed when the test ends.
struct TempJson {
    path: PathBuf,
}

impl TempJson {
    fn new(tag: &str, contents: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "std-deduce-definitions-{}-{tag}-{}.json",
            std::process::id(),
            next_suffix()
        ));
        fs::write(&path, contents).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempJson { path }
    }

    fn path_str(&self) -> String {
        self.path.display().to_string()
    }
}

impl Drop for TempJson {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}
