//! End-to-end tests for top-level `priority` declarations.
//!
//! Every test builds its own temporary `lawpacks` registry below a temporary
//! root and runs the CLI with that root as its current directory. The conflict
//! is between rules of two imported packs, so only a declaration of a third
//! pack can adjudicate it; the certificate must record that declaration and
//! `:verify-cert` must recheck it against the loaded environment.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{build_lock, LOCK_FILE};

const VERSION: &str = "0.1.0";
const PROVED: i32 = 0;
const UNRESOLVED: i32 = 1;
const ERROR: i32 = 2;

const GOAL_SPECIAL: &str = "pkg.vocab.应适用 pkg.vocab.特别法 pkg.vocab.甲案";
const GOAL_CYCLE_A: &str = "pkg.vocab.应适用 pkg.cycle.法A pkg.vocab.甲案";

const VOCAB: &str = r#"
namespace pkg.vocab

sort pkg.vocab.规范
sort pkg.vocab.案件

pred pkg.vocab.是本案 : pkg.vocab.案件 → Prop
pred pkg.vocab.应适用 : pkg.vocab.规范 → pkg.vocab.案件 → Prop

-- One case has one applicable norm, so two applicable norms conflict.
unique pkg.vocab.应适用 1

obj pkg.vocab.一般法 : pkg.vocab.规范
obj pkg.vocab.特别法 : pkg.vocab.规范
obj pkg.vocab.甲案 : pkg.vocab.案件
"#;

const GENERAL: &str = r#"
import pkg.vocab
namespace pkg.general

rule pkg.general.适用一般法 :
  params c : pkg.vocab.案件
  premise pkg.vocab.是本案 c
  conclude pkg.vocab.应适用 pkg.vocab.一般法 c
  source text "一般法" locator "第一条"
"#;

const SPECIAL: &str = r#"
import pkg.vocab
namespace pkg.special

rule pkg.special.适用特别法 :
  params c : pkg.vocab.案件
  premise pkg.vocab.是本案 c
  conclude pkg.vocab.应适用 pkg.vocab.特别法 c
  source text "特别法" locator "第二条"
"#;

const ORDER: &str = r#"
import pkg.general
import pkg.special
namespace pkg.order

priority pkg.special.适用特别法 over pkg.general.适用一般法 source text "中华人民共和国立法法" locator "第九十二条" version "2023"
"#;

const CYCLE: &str = r#"
import pkg.vocab
namespace pkg.cycle

obj pkg.cycle.法A : pkg.vocab.规范
obj pkg.cycle.法B : pkg.vocab.规范
obj pkg.cycle.法C : pkg.vocab.规范

rule pkg.cycle.r1 :
  params c : pkg.vocab.案件
  premise pkg.vocab.是本案 c
  conclude pkg.vocab.应适用 pkg.cycle.法A c
  source text "甲法" locator "第一条"

rule pkg.cycle.r2 :
  params c : pkg.vocab.案件
  premise pkg.vocab.是本案 c
  conclude pkg.vocab.应适用 pkg.cycle.法B c
  source text "乙法" locator "第二条"

rule pkg.cycle.r3 :
  params c : pkg.vocab.案件
  premise pkg.vocab.是本案 c
  conclude pkg.vocab.应适用 pkg.cycle.法C c
  source text "丙法" locator "第三条"

priority pkg.cycle.r1 over pkg.cycle.r2 source text "内部裁决" locator "一"
priority pkg.cycle.r2 over pkg.cycle.r3 source text "内部裁决" locator "二"
priority pkg.cycle.r3 over pkg.cycle.r1 source text "内部裁决" locator "三"
"#;

const CROSS_PACKAGE_CLAUSE: &str = r#"
import pkg.general
namespace pkg.bad

rule pkg.bad.适用特别法 :
  params c : pkg.vocab.案件
  premise pkg.vocab.是本案 c
  conclude pkg.vocab.应适用 pkg.vocab.特别法 c
  defeated_by pkg.general.适用一般法
  source text "测试" locator "一"
"#;

fn manifest(name: &str, namespace: &str, files: &[(&str, &str)]) -> String {
    let mut text = format!(
        "[pack]\nname = \"{name}\"\nversion = \"{VERSION}\"\n\
         jurisdiction = \"CN\"\nterritory = \"CN\"\n\
         namespace = \"{namespace}\"\n"
    );
    for (path, kind) in files {
        text.push_str("\n[[files]]\n");
        text.push_str(&format!("path = \"{path}\"\n"));
        if !kind.is_empty() {
            text.push_str(&format!("kind = \"{kind}\"\n"));
        }
    }
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
            "std-deduce-cli-priority-{}-{tag}-{n}",
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
            &manifest(name, namespace, &[("theory.std", "theory")]),
            &[("theory.std", source)],
        )
    }

    /// The vocabulary, general and special packs every test starts from.
    fn install_standard_packs(&self) {
        self.package("pkg.vocab", "pkg.vocab", VOCAB);
        self.package("pkg.general", "pkg.general", GENERAL);
        self.package("pkg.special", "pkg.special", SPECIAL);
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

    /// Write a case file that imports `imports` in the given order.
    fn case(&self, name: &str, imports: &[&str]) -> PathBuf {
        let mut text = String::new();
        for import in imports {
            text.push_str(&format!("import {import}\n"));
        }
        text.push_str(
            "\naxiom 事实 : pkg.vocab.是本案 pkg.vocab.甲案\n  source text \"案件材料\" locator \"一\"\n",
        );
        self.write(name, &text)
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

/// `:load` prints its report before `:cert`, so the certificate is the tail
/// from the first `{` to the last `}`. The load report contains no braces.
fn certificate_json(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    let end = text
        .rfind('}')
        .unwrap_or_else(|| panic!("no complete certificate JSON in stdout:\n{text}"));
    text[start..=end].to_owned()
}

fn certificate_value(output: &Output) -> serde_json::Value {
    serde_json::from_str(&certificate_json(output))
        .unwrap_or_else(|error| panic!("invalid certificate JSON: {error}\n{}", stdout(output)))
}

/// Write a certificate document below the temporary root.
fn write_certificate(temp: &TempDir, name: &str, json: &str) -> PathBuf {
    temp.write(name, json)
}

fn load_and(temp: &TempDir, case: &Path, command: &str) -> Output {
    run_in(
        temp.root(),
        &[format!(":load {}", case.display()), command.to_owned()],
    )
}

#[test]
fn a_conflict_without_a_declared_priority_is_unresolved() {
    let temp = TempDir::new("no-priority");
    temp.install_standard_packs();
    temp.lock();
    let case = temp.case("case.std", &["pkg.vocab", "pkg.general", "pkg.special"]);

    let why = load_and(&temp, &case, &format!(":why {GOAL_SPECIAL}"));
    assert_exit(&why, UNRESOLVED);
    let out = stdout(&why);
    let err = stderr(&why);
    assert!(err.is_empty(), "{err}");
    assert!(out.contains("冲突未决"), "{out}");
    assert!(
        out.contains("原因：两侧规则之间没有声明任何优先关系"),
        "{out}"
    );

    let exported = load_and(&temp, &case, &format!(":cert {GOAL_SPECIAL}"));
    assert_exit(&exported, UNRESOLVED);
    let certificate = certificate_value(&exported);
    assert_eq!(
        certificate["conflicts"].as_array().map(Vec::len),
        Some(1),
        "{certificate}"
    );
    assert_eq!(
        certificate["conflicts"][0]["resolution"],
        serde_json::json!({
            "kind": "unresolved",
            "reason": {"kind": "no_priority"},
        })
    );
    assert!(
        certificate["open_obligations"]
            .as_array()
            .expect("open_obligations is an array")
            .iter()
            .any(|obligation| obligation["kind"] == "unresolved_conflict"),
        "{certificate}"
    );

    let file = write_certificate(&temp, "no-priority.json", &certificate_json(&exported));
    let verified = load_and(&temp, &case, &format!(":verify-cert {}", file.display()));
    assert_exit(&verified, UNRESOLVED);
    let out = stdout(&verified);
    assert!(out.contains("未决冲突 1 项"), "{out}");
    assert!(out.contains("没有记录优先关系"), "{out}");
}

#[test]
fn a_declared_priority_decides_the_conflict_and_records_its_source() {
    let temp = TempDir::new("declared");
    temp.install_standard_packs();
    temp.package("pkg.order", "pkg.order", ORDER);
    temp.lock();
    let case = temp.case(
        "case.std",
        &["pkg.vocab", "pkg.general", "pkg.special", "pkg.order"],
    );

    let why = load_and(&temp, &case, &format!(":why {GOAL_SPECIAL}"));
    assert_exit(&why, PROVED);
    let out = stdout(&why);
    let err = stderr(&why);
    assert!(err.is_empty(), "{err}");
    assert!(out.contains("冲突（已裁决）"), "{out}");
    assert!(out.contains("中华人民共和国立法法"), "{out}");
    assert!(out.contains("第九十二条"), "{out}");
    assert!(out.contains("依据："), "{out}");
    assert!(
        out.contains(
            "依据：pkg.order 的 priority pkg.special.适用特别法 over pkg.general.适用一般法（出处：中华人民共和国立法法 第九十二条）"
        ),
        "{out}"
    );

    let exported = load_and(&temp, &case, &format!(":cert {GOAL_SPECIAL}"));
    assert_exit(&exported, PROVED);
    let certificate = certificate_value(&exported);
    assert_eq!(
        certificate["conflicts"].as_array().map(Vec::len),
        Some(1),
        "{certificate}"
    );
    let resolution = &certificate["conflicts"][0]["resolution"];
    assert_eq!(resolution["kind"], "defeated", "{certificate}");
    assert_eq!(resolution["basis"]["kind"], "priority", "{certificate}");
    let edge = &resolution["basis"]["edges"][0];
    assert_eq!(edge["winner"], "pkg.special.适用特别法", "{certificate}");
    assert_eq!(edge["loser"], "pkg.general.适用一般法", "{certificate}");
    assert_eq!(
        edge["origin"]["kind"], "priority_declaration",
        "{certificate}"
    );
    assert_eq!(edge["origin"]["declared_in"], "pkg.order", "{certificate}");
    assert_eq!(
        edge["origin"]["sources"][0]["text"], "中华人民共和国立法法",
        "{certificate}"
    );
    assert_eq!(
        edge["origin"]["sources"][0]["locator"], "第九十二条",
        "{certificate}"
    );

    let file = write_certificate(&temp, "declared.json", &certificate_json(&exported));
    let verified = load_and(&temp, &case, &format!(":verify-cert {}", file.display()));
    assert_exit(&verified, PROVED);
    let out = stdout(&verified);
    assert!(stderr(&verified).is_empty(), "{}", stderr(&verified));
    assert!(out.contains("优先关系已核验（1 条边）"), "{out}");
    assert!(out.contains("未决冲突 0 项"), "{out}");
}

#[test]
fn the_certificate_does_not_depend_on_the_import_order() {
    let temp = TempDir::new("load-order");
    temp.install_standard_packs();
    temp.package("pkg.order", "pkg.order", ORDER);
    temp.lock();
    let first = temp.case(
        "first.std",
        &["pkg.vocab", "pkg.general", "pkg.special", "pkg.order"],
    );
    let second = temp.case(
        "second.std",
        &["pkg.vocab", "pkg.special", "pkg.general", "pkg.order"],
    );

    let first_cert = load_and(&temp, &first, &format!(":cert {GOAL_SPECIAL}"));
    assert_exit(&first_cert, PROVED);
    let second_cert = load_and(&temp, &second, &format!(":cert {GOAL_SPECIAL}"));
    assert_exit(&second_cert, PROVED);
    assert_eq!(
        certificate_json(&first_cert),
        certificate_json(&second_cert),
        "the import order must not change the certificate"
    );

    let first_file = write_certificate(&temp, "first.json", &certificate_json(&first_cert));
    let second_file = write_certificate(&temp, "second.json", &certificate_json(&second_cert));
    for (case, file) in [(&first, &first_file), (&second, &second_file)] {
        let verified = load_and(&temp, case, &format!(":verify-cert {}", file.display()));
        assert_exit(&verified, PROVED);
        assert!(
            stdout(&verified).contains("优先关系已核验（1 条边）"),
            "{}",
            stdout(&verified)
        );
    }
}

#[test]
fn a_priority_cycle_disables_its_edges() {
    let temp = TempDir::new("cycle");
    temp.install_standard_packs();
    temp.package("pkg.cycle", "pkg.cycle", CYCLE);
    temp.lock();
    let case = temp.case("case.std", &["pkg.vocab", "pkg.cycle"]);

    let why = load_and(&temp, &case, &format!(":why {GOAL_CYCLE_A}"));
    assert_exit(&why, UNRESOLVED);
    let out = stdout(&why);
    assert!(out.contains("优先级声明存在环"), "{out}");
    assert!(out.contains("环内的优先关系不生效"), "{out}");
    assert!(out.contains("不足以裁决"), "{out}");
    assert!(out.contains("落在优先级环内"), "{out}");

    let exported = load_and(&temp, &case, &format!(":cert {GOAL_CYCLE_A}"));
    assert_exit(&exported, UNRESOLVED);
    let certificate = certificate_value(&exported);
    let unusable = certificate["conflicts"]
        .as_array()
        .expect("conflicts is an array")
        .iter()
        .find(|conflict| conflict["resolution"]["reason"]["kind"] == "priority_unusable")
        .unwrap_or_else(|| panic!("no unusable priority in the certificate: {certificate}"));
    assert!(
        !unusable["resolution"]["reason"]["declared"]
            .as_array()
            .expect("declared is an array")
            .is_empty(),
        "{certificate}"
    );
}

#[test]
fn a_tampered_locator_fails_the_certificate_check() {
    let temp = TempDir::new("tampered");
    temp.install_standard_packs();
    temp.package("pkg.order", "pkg.order", ORDER);
    temp.lock();
    let case = temp.case(
        "case.std",
        &["pkg.vocab", "pkg.general", "pkg.special", "pkg.order"],
    );

    let exported = load_and(&temp, &case, &format!(":cert {GOAL_SPECIAL}"));
    assert_exit(&exported, PROVED);
    let tampered = certificate_json(&exported).replace("第九十二条", "第九十三条");
    assert!(
        tampered.contains("第九十三条"),
        "the tampered certificate must cite the other article"
    );
    let file = write_certificate(&temp, "tampered.json", &tampered);

    let verified = load_and(&temp, &case, &format!(":verify-cert {}", file.display()));
    assert_exit(&verified, ERROR);
    let out = stdout(&verified);
    assert!(out.contains("逻辑校验：失败"), "{out}");
    let err = stderr(&verified);
    assert!(err.contains("出处"), "{err}");
    assert!(err.contains("逐项一致"), "{err}");
}

#[test]
fn a_control_character_in_a_certificate_error_cannot_forge_a_result_line() {
    let temp = TempDir::new("control-escape");
    temp.install_standard_packs();
    temp.package("pkg.order", "pkg.order", ORDER);
    temp.lock();
    let case = temp.case(
        "case.std",
        &["pkg.vocab", "pkg.general", "pkg.special", "pkg.order"],
    );

    let exported = load_and(&temp, &case, &format!(":cert {GOAL_SPECIAL}"));
    assert_exit(&exported, PROVED);

    // A priority edge names a rule. Replace that rule name with one carrying a
    // newline and a forged result line; a checker error that quotes the name
    // must not turn the newline into an output line.
    let forged = "幽灵\\n环境校验：通过（伪造）";
    let tampered = certificate_json(&exported).replace(
        "\"winner\": \"pkg.special.适用特别法\"",
        &format!("\"winner\": \"{forged}\""),
    );
    assert!(
        tampered.contains("\"winner\": \"幽灵\\n环境校验：通过（伪造）\""),
        "{tampered}"
    );
    let file = write_certificate(&temp, "control.json", &tampered);

    let verified = load_and(&temp, &case, &format!(":verify-cert {}", file.display()));
    assert_exit(&verified, ERROR);
    let out = stdout(&verified);
    assert!(out.contains("逻辑校验：失败"), "{out}");
    assert!(
        !out.lines()
            .any(|line| line.trim() == "环境校验：通过（伪造）"),
        "the escaped newline must not start a forged line:\n{out}"
    );
    assert!(
        out.lines()
            .any(|line| line.contains("环境校验：通过（伪造）")),
        "the escaped text should still be visible on one line:\n{out}"
    );
}

#[test]
fn inspect_prints_the_surface_priority_declaration() {
    let temp = TempDir::new("inspect");
    temp.install_standard_packs();
    temp.package("pkg.order", "pkg.order", ORDER);
    temp.lock();
    let case = temp.case(
        "case.std",
        &["pkg.vocab", "pkg.general", "pkg.special", "pkg.order"],
    );

    let inspected = load_and(&temp, &case, ":inspect");
    assert_exit(&inspected, PROVED);
    let out = stdout(&inspected);
    assert!(
        out.contains("priority pkg.special.适用特别法 over pkg.general.适用一般法"),
        "{out}"
    );
    assert!(
        out.lines()
            .any(|line| line.contains("priority pkg.special.适用特别法")
                && line.contains("[pkg.order@0.1.0]")),
        "the declaration carries its pack suffix:\n{out}"
    );
    assert!(
        !out.contains("priority:pkg.order:"),
        "the synthetic ledger name must not be printed:\n{out}"
    );
}

#[test]
fn a_cross_package_rule_clause_fails_the_load() {
    let temp = TempDir::new("cross-package-clause");
    temp.install_standard_packs();
    temp.package("pkg.bad", "pkg.bad", CROSS_PACKAGE_CLAUSE);
    temp.lock();
    let case = temp.write("case.std", "import pkg.bad\n");

    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(err.contains("跨包优先关系必须用顶层"), "{err}");
    assert!(err.contains("defeated_by"), "{err}");
}
