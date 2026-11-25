//! End-to-end tests for the effective-date and jurisdiction metadata and the
//! temporal/spatial applicability judgement.
//!
//! The first group pins the syntax, pack-manifest inheritance, `:inspect`
//! output, the session `:asof` / `:jurisdiction` commands and the
//! certificate's recorded identity. The second group pins the judgement: an
//! inapplicable rule does not fire, `:gap` reports excluded candidates,
//! `:applicability` lists the verdicts, and an unchecked verdict keeps the old
//! conclusion but is labelled.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{build_lock, LOCK_FILE};

const PROVED: i32 = 0;
const GAP: i32 = 1;
const LOAD_FAILED: i32 = 1;
const ERROR: i32 = 2;

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

/// Assert the exit code; return the whole output for further assertions.
fn assert_exit(output: &Output, expected: i32) {
    assert_eq!(
        output.status.code(),
        Some(expected),
        "expected exit {expected}, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout(output),
        stderr(output)
    );
}

/// Parse the certificate JSON that starts at the first `{` in `out`.
fn certificate_json(out: &str) -> serde_json::Value {
    let start = out
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON:\n{out}"));
    serde_json::from_str(&out[start..])
        .unwrap_or_else(|error| panic!("the certificate is not JSON: {error}\n{}", &out[start..]))
}

fn line_containing<'a>(out: &'a str, needle: &str) -> &'a str {
    out.lines()
        .find(|line| line.contains(needle))
        .unwrap_or_else(|| panic!("no output line contains {needle:?}\n{out}"))
}

/// A temporary tree holding the theory, the case and, when needed, a registry.
struct TempRoot {
    path: PathBuf,
}

impl TempRoot {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-scope-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempRoot { path }
    }

    fn root(&self) -> &Path {
        &self.path
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
        let dir = self.path.join("lawpacks").join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join("lawpack.toml"), manifest)
            .unwrap_or_else(|error| panic!("write manifest: {error}"));
        for (relative, text) in files {
            let path = dir.join(relative);
            fs::write(&path, text)
                .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        }
        dir
    }

    fn lock(&self) {
        let root = self.path.join("lawpacks");
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

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

/// A plain case theory with explicit scope clauses on one rule and one fact.
fn scoped_theory() -> String {
    r#"
sort 人
pred 犯规 : 人 → Prop
pred 处罚 : 人 → Prop
pred 免责 : 人 → Prop
obj 甲 : 人

axiom 事实 : 犯规 甲
  source text "案件材料" locator "第一页"
  occurred_at 2020-05-06
  occurred_in CN-HN

rule 已废止规则 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  effective 1999-10-01
  repealed 2021-01-01
  jurisdiction CN
  territory CN-HN
  source text "测试法" locator "第一条"

rule 无作用域规则 :
  params x : 人
  premise 免责 x
  conclude 处罚 x
  source text "测试法" locator "第二条"
"#
    .to_owned()
}

/// `:inspect` shows the declared scope after the identity, never a defaulted
/// placeholder, and a fact's occurrence is shown too.
#[test]
fn inspect_shows_declared_scope_and_occurrence_without_placeholders() {
    let temp = TempRoot::new("inspect");
    let theory = temp.write("case.std", &scoped_theory());
    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":inspect".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);

    let scoped = line_containing(&out, "rule  已废止规则 :");
    assert!(
        scoped.contains(
            "〔生效 1999-10-01..2021-01-01（规则）〕〔管辖 CN（规则）〕〔地域 CN-HN（规则）〕"
        ),
        "the rule line must show the declared scope and its provenance: {scoped:?}"
    );
    let fact = line_containing(&out, "fact  事实 :");
    assert!(
        fact.contains("〔发生 2020-05-06〕〔发生地 CN-HN〕"),
        "the fact line must show the declared occurrence: {fact:?}"
    );
    assert!(
        fact.contains("〔用户陈述〕"),
        "the identity label stays on the line: {fact:?}"
    );

    let unscoped = line_containing(&out, "rule  无作用域规则 :");
    for placeholder in ["〔生效", "〔管辖", "〔地域", "默认", "（规则）", "（继承）"]
    {
        assert!(
            !unscoped.contains(placeholder),
            "an undeclared scope must not be filled in ({placeholder}): {unscoped:?}"
        );
    }
}

/// Loading rules and facts with the wrong clause kind is a load error, not a
/// silently ignored line.
#[test]
fn scope_and_occurrence_clauses_are_refused_on_the_wrong_declaration_kind() {
    let temp = TempRoot::new("wrong-kind");
    let rule_with_occurrence = temp.write(
        "rule-occurrence.std",
        r#"
sort 人
pred 犯规 : 人 → Prop
pred 处罚 : 人 → Prop
rule 规则 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  occurred_at 2020-05-06
  source text "测试法" locator "第一条"
"#,
    );
    let output = run_in(temp.root(), &[rule_with_occurrence.display().to_string()]);
    assert_exit(&output, LOAD_FAILED);
    let err = stderr(&output);
    assert!(
        err.contains("occurred_at") && err.contains("事实"),
        "a rule must be told that occurred_at belongs to facts: {err}"
    );

    let fact_with_effective = temp.write(
        "fact-effective.std",
        r#"
sort 人
pred 犯规 : 人 → Prop
obj 甲 : 人
axiom 事实 : 犯规 甲
  effective 1999-10-01
  source text "案件材料" locator "第一页"
"#,
    );
    let output = run_in(temp.root(), &[fact_with_effective.display().to_string()]);
    assert_exit(&output, LOAD_FAILED);
    let err = stderr(&output);
    assert!(
        err.contains("effective") && err.contains("规则"),
        "a fact must be told that effective belongs to rules: {err}"
    );
}

/// `repealed` must have an `effective` start and come after it; a bad date or
/// jurisdiction code is refused with the same validators as `--as-of` /
/// `--jurisdiction`.
#[test]
fn invalid_scope_values_are_load_errors() {
    let cases = [
        (
            "repealed-without-effective",
            "  repealed 2021-01-01\n",
            "起点",
            "effective",
        ),
        (
            "repealed-not-later",
            "  effective 2021-01-01\n  repealed 2021-01-01\n",
            "生效起点",
            "失效日",
        ),
        ("bad-date", "  effective 2021-02-30\n", "effective", "日期"),
        (
            "bad-jurisdiction",
            "  jurisdiction CN_HN\n",
            "jurisdiction",
            "非法字符",
        ),
    ];
    let temp = TempRoot::new("bad-scope");
    for (tag, clause, needle_a, needle_b) in cases {
        let source = format!(
            "sort 人\npred 犯规 : 人 → Prop\npred 处罚 : 人 → Prop\n\
             rule 规则 :\n  params x : 人\n  premise 犯规 x\n  conclude 处罚 x\n\
             {clause}  source text \"测试法\" locator \"第一条\"\n"
        );
        let theory = temp.write(&format!("{tag}.std"), &source);
        let output = run_in(temp.root(), &[theory.display().to_string()]);
        assert_exit(&output, LOAD_FAILED);
        let err = stderr(&output);
        assert!(
            err.contains(needle_a) && err.contains(needle_b),
            "{tag}: the error must name {needle_a:?} and {needle_b:?}: {err}"
        );
        assert!(
            err.contains("`rule 规则`"),
            "{tag}: the load error must name the rule: {err}"
        );
    }
}

/// A rule inside a law pack inherits the manifest's jurisdiction, territory and
/// effective range field by field; a field the rule declares itself wins.
#[test]
fn pack_rules_inherit_the_manifest_scope_field_by_field() {
    let temp = TempRoot::new("inherit");
    let manifest = "[pack]\n\
                    name = \"pkg.a\"\n\
                    version = \"0.1.0\"\n\
                    jurisdiction = \"CN\"\n\
                    territory = \"CN\"\n\
                    effective_from = \"1999-10-01\"\n\
                    effective_to = \"2021-01-01\"\n\
                    namespace = \"pkg.a\"\n\
                    \n[[files]]\npath = \"theory.std\"\nkind = \"theory\"\n";
    let theory = r#"
namespace pkg.a
sort pkg.a.人
pred pkg.a.犯规 : pkg.a.人 → Prop
pred pkg.a.处罚 : pkg.a.人 → Prop
rule pkg.a.继承 :
  params x : pkg.a.人
  premise pkg.a.犯规 x
  conclude pkg.a.处罚 x
  source text "测试法" locator "第一条"
rule pkg.a.显式 :
  params x : pkg.a.人
  premise pkg.a.犯规 x
  conclude pkg.a.处罚 x
  territory CN-HN
  source text "测试法" locator "第二条"
rule pkg.a.继承起点 :
  params x : pkg.a.人
  premise pkg.a.犯规 x
  conclude pkg.a.处罚 x
  repealed 2020-01-01
  source text "测试法" locator "第三条"
"#;
    temp.write_pack("pkg.a", manifest, &[("theory.std", theory)]);
    temp.lock();
    let case = temp.write(
        "case.std",
        "import pkg.a\nobj 甲 : pkg.a.人\n\
         axiom 事实 : pkg.a.犯规 甲\n  source text \"案件材料\" locator \"第一页\"\n",
    );

    let output = run_in(
        temp.root(),
        &[format!(":load {}", case.display()), ":inspect".to_string()],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);

    let inherited = line_containing(&out, "rule  pkg.a.继承 :");
    assert!(
        inherited.contains(
            "〔生效 1999-10-01..2021-01-01（继承）〕〔管辖 CN（继承）〕〔地域 CN（继承）〕"
        ),
        "the whole manifest scope is inherited: {inherited:?}"
    );
    let explicit = line_containing(&out, "rule  pkg.a.显式 :");
    assert!(
        explicit.contains(
            "〔生效 1999-10-01..2021-01-01（继承）〕〔管辖 CN（继承）〕〔地域 CN-HN（规则）〕"
        ),
        "the explicit territory wins and the rest is inherited: {explicit:?}"
    );
    // A rule may write only `repealed`; its start comes from the manifest, and
    // the two endpoints keep different provenance markers.
    let inherited_start = line_containing(&out, "rule  pkg.a.继承起点 :");
    assert!(
        inherited_start.contains(
            "〔生效 1999-10-01..2020-01-01（继承/规则）〕〔管辖 CN（继承）〕〔地域 CN（继承）〕"
        ),
        "a written repealed takes the manifest start and keeps both origins: {inherited_start:?}"
    );
}

/// A merged interval with the rule's start after the manifest's end is refused
/// at load time, naming the rule and both dates.
#[test]
fn a_pack_rule_start_after_the_manifest_end_is_refused() {
    let temp = TempRoot::new("merged-out-of-range");
    let manifest = "[pack]\n\
                    name = \"pkg.a\"\n\
                    version = \"0.1.0\"\n\
                    jurisdiction = \"CN\"\n\
                    territory = \"CN\"\n\
                    effective_from = \"1999-10-01\"\n\
                    effective_to = \"2001-01-01\"\n\
                    namespace = \"pkg.a\"\n\
                    \n[[files]]\npath = \"theory.std\"\nkind = \"theory\"\n";
    let theory = r#"
namespace pkg.a
sort pkg.a.人
pred pkg.a.犯规 : pkg.a.人 → Prop
pred pkg.a.处罚 : pkg.a.人 → Prop
rule pkg.a.越界 :
  params x : pkg.a.人
  premise pkg.a.犯规 x
  conclude pkg.a.处罚 x
  effective 2005-01-01
  source text "测试法" locator "第一条"
"#;
    temp.write_pack("pkg.a", manifest, &[("theory.std", theory)]);
    temp.lock();
    let case = temp.write(
        "case.std",
        "import pkg.a\nobj 甲 : pkg.a.人\n\
         axiom 事实 : pkg.a.犯规 甲\n  source text \"案件材料\" locator \"第一页\"\n",
    );
    let output = run_in(temp.root(), &[format!(":load {}", case.display())]);
    // A pack that fails to load is an environment/usage error and exits `2`,
    // like the other registry and lock failures.
    assert_exit(&output, ERROR);
    let err = stderr(&output);
    assert!(
        err.contains("pkg.a.越界") && err.contains("2005-01-01") && err.contains("2001-01-01"),
        "the load error must name the rule and both dates: {err}"
    );
}

/// `:asof` / `:jurisdiction` with no argument print the current value and where
/// it came from; with an argument they set the same session value the
/// certificate records.
#[test]
fn asof_and_jurisdiction_commands_report_and_set_the_session_value() {
    let temp = TempRoot::new("commands");
    let theory = temp.write("case.std", &scoped_theory());

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof".to_string(),
            ":jurisdiction".to_string(),
            ":asof 2026-11-23".to_string(),
            ":jurisdiction CN".to_string(),
            ":asof".to_string(),
            ":jurisdiction".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("基准日：未设置"), "{out}");
    assert!(out.contains("管辖：未设置"), "{out}");
    assert!(out.contains("基准日：2026-11-23（会话命令）"), "{out}");
    assert!(out.contains("管辖：CN（会话命令）"), "{out}");

    // A bad value is a command error, and the old value stays in effect.
    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2026-02-30".to_string(),
        ],
    );
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains("日期"), "{}", stderr(&output));

    // The value given on the command line is reported as `命令行`; a later
    // session command replaces it and is reported as `会话命令`.
    let output = run_in(
        temp.root(),
        &[
            "--as-of".to_string(),
            "2026-11-23".to_string(),
            "--jurisdiction".to_string(),
            "CN".to_string(),
            format!(":load {}", theory.display()),
            ":asof".to_string(),
            ":jurisdiction".to_string(),
            ":asof 2020-01-01".to_string(),
            ":asof".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("基准日：2026-11-23（命令行）"), "{out}");
    assert!(out.contains("管辖：CN（命令行）"), "{out}");
    assert!(out.contains("基准日：2020-01-01（会话命令）"), "{out}");
}

/// The certificate records the value the session commands set, and
/// `:verify-cert` compares against the same session value. The date is chosen
/// inside the rule's effective range so the rule is applicable and `:cert`
/// proves the goal.
#[test]
fn cert_records_the_session_asof_and_jurisdiction() {
    let temp = TempRoot::new("cert-record");
    let theory = temp.write("case.std", &scoped_theory());
    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2020-06-01".to_string(),
            ":jurisdiction CN".to_string(),
            ":cert 处罚 甲".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let json = &out[out.find('{').expect("the certificate JSON starts")..];
    let value: serde_json::Value = serde_json::from_str(json).expect("the certificate is JSON");
    assert_eq!(value["environment"]["as_of"], "2020-06-01");
    assert_eq!(value["environment"]["jurisdiction"], "CN");
    let cert_path = temp.write("cert.json", json);

    // The same session values on a fresh session verify the certificate.
    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2020-06-01".to_string(),
            ":jurisdiction CN".to_string(),
            format!(":verify-cert {}", cert_path.display()),
        ],
    );
    assert_exit(&output, PROVED);
    assert!(
        stdout(&output).contains("环境校验：通过"),
        "{}",
        stdout(&output)
    );

    // Without them the recorded identity no longer matches.
    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            format!(":verify-cert {}", cert_path.display()),
        ],
    );
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(
        out.contains("环境校验：失败") && out.contains("as_of 不一致"),
        "the environment differences are printed on stdout:\n{out}\nstderr:\n{}",
        stderr(&output)
    );
}

/// With no `:asof`, the rule's recorded facts keep it inside its range and an
/// unchecked jurisdiction verdict does not block it: the conclusion and the
/// exit code stay what they were, and the state is printed. A later date
/// outside the range makes the rule inapplicable, so the conclusion disappears
/// and the reason is readable.
#[test]
fn asof_judges_applicability_and_an_unchecked_rule_still_fires() {
    let temp = TempRoot::new("asof-judges");
    let theory = temp.write("case.std", &scoped_theory());

    let plain = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 处罚 甲".to_string(),
        ],
    );
    assert_exit(&plain, PROVED);
    let plain_out = stdout(&plain);
    assert!(
        plain_out.contains("▸ 处罚 甲"),
        "an unchecked rule still fires:\n{plain_out}"
    );
    assert!(
        plain_out.contains(
            "时空适用性：\n  ⟨已废止规则⟩：适用性未判定（规则声明了管辖，但会话未设置 :jurisdiction）"
        ),
        "an unchecked judgement must be labelled:\n{plain_out}"
    );
    // The derivation part is the old one; only the applicability block is new.
    let tree = |out: &str| -> String {
        let start = out
            .find("▸")
            .unwrap_or_else(|| panic!("no derivation tree:\n{out}"));
        out[start..]
            .split("\n\n")
            .next()
            .unwrap_or_default()
            .to_owned()
    };

    // A date inside the range plus the matching jurisdiction is a positive
    // judgement: the same tree, no warning.
    let applicable = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2020-01-01".to_string(),
            ":jurisdiction CN".to_string(),
            ":why 处罚 甲".to_string(),
        ],
    );
    assert_exit(&applicable, PROVED);
    let applicable_out = stdout(&applicable);
    assert!(
        !applicable_out.contains("时空适用性："),
        "a fully applicable rule needs no applicability block:\n{applicable_out}"
    );
    assert_eq!(
        tree(&plain_out),
        tree(&applicable_out),
        "an applicable rule's derivation tree must be the old one"
    );

    // A query date at the rule's repeal day makes it inapplicable.
    let repealed = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":jurisdiction CN".to_string(),
            ":why 处罚 甲".to_string(),
        ],
    );
    assert_exit(&repealed, GAP);
    let repealed_out = stdout(&repealed);
    assert!(
        repealed_out.contains("证书有效，但根为缺口，结论未被证明。"),
        "{repealed_out}"
    );
    assert!(
        repealed_out.contains(
            "⟨已废止规则⟩：不适用（案件日期 2022-01-01 已达到规则废止日 2021-01-01，规则已经失效）"
        ),
        "the reason names the date that excluded the rule:\n{repealed_out}"
    );

    // `:gap` lists the excluded candidate instead of hiding it.
    let gap = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":jurisdiction CN".to_string(),
            ":gap 处罚 甲".to_string(),
        ],
    );
    assert_exit(&gap, GAP);
    let gap_out = stdout(&gap);
    assert!(
        gap_out.contains("候选 ⟨已废止规则⟩〔不适用（案件日期 2022-01-01"),
        "an inapplicable candidate is listed with its reason:\n{gap_out}"
    );
    assert!(
        gap_out.contains("候选 ⟨无作用域规则⟩〔适用性未判定（规则没有声明任何范围）〕"),
        "an unscoped candidate is shown as unchecked:\n{gap_out}"
    );

    // `:cert` records the date by design, but an applicable date leaves the
    // proof (assumptions, nodes, root) untouched.
    let plain_cert = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":cert 处罚 甲".to_string(),
        ],
    );
    let dated_cert = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2020-01-01".to_string(),
            ":jurisdiction CN".to_string(),
            ":cert 处罚 甲".to_string(),
        ],
    );
    assert_exit(&plain_cert, PROVED);
    assert_exit(&dated_cert, PROVED);
    let plain_json = certificate_json(&stdout(&plain_cert));
    let dated_json = certificate_json(&stdout(&dated_cert));
    for field in ["assumptions", "nodes", "root", "conflicts"] {
        assert_eq!(
            plain_json[field], dated_json[field],
            "an applicable date must not change the certificate's {field}"
        );
    }
    assert!(plain_json["environment"]["as_of"].is_null());
    assert_eq!(dated_json["environment"]["as_of"], "2020-01-01");
}

/// A contract signed in 2019 cannot be governed by a rule that entered into
/// force in 2021: the rule is inapplicable on the recorded occurrence date,
/// even at a later as-of date, and it never derives its conclusion.
#[test]
fn a_rule_that_starts_after_the_case_is_inapplicable_and_does_not_fire() {
    let temp = TempRoot::new("late-rule");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 已签订合同 : 人 → Prop
pred 可撤销 : 人 → Prop
obj 甲 : 人
axiom 合同签订 : 已签订合同 甲
  source text "合同" locator "第一条"
  occurred_at 2019-05-01
rule 二〇二一年生效规则 :
  params x : 人
  premise 已签订合同 x
  conclude 可撤销 x
  effective 2021-01-01
  source text "民法典" locator "第一百四十七条"
"#,
    );

    // No as-of date: the recorded occurrence date is the reference date and
    // already excludes the rule.
    let plain = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 可撤销 甲".to_string(),
        ],
    );
    assert_exit(&plain, GAP);
    let plain_out = stdout(&plain);
    assert!(
        plain_out.contains(
            "⟨二〇二一年生效规则⟩：不适用（案件日期 2019-05-01 早于规则生效日 2021-01-01，规则当时尚未生效）"
        ),
        "{plain_out}"
    );

    // `:asof 2019-…`: the query date names the same exclusion.
    let dated = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2019-06-01".to_string(),
            ":why 可撤销 甲".to_string(),
        ],
    );
    assert_exit(&dated, GAP);
    let dated_out = stdout(&dated);
    assert!(
        dated_out.contains(
            "⟨二〇二一年生效规则⟩：不适用（案件日期 2019-06-01 早于规则生效日 2021-01-01，规则当时尚未生效）"
        ),
        "{dated_out}"
    );

    // A later as-of date does not revive the rule: the fact still happened
    // before its start.
    let later = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":why 可撤销 甲".to_string(),
        ],
    );
    assert_exit(&later, GAP);
    let later_out = stdout(&later);
    assert!(
        later_out.contains("案件日期 2019-05-01 早于规则生效日 2021-01-01"),
        "{later_out}"
    );

    // `:applicability <goal>` reports the verdict and always exits 0.
    let report = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":applicability 可撤销 甲".to_string(),
        ],
    );
    assert_exit(&report, PROVED);
    let report_out = stdout(&report);
    assert!(
        report_out.contains(
            "时空适用性（目标：可撤销 甲）：\n  ⟨二〇二一年生效规则⟩：不适用（案件日期 2019-05-01"
        ),
        "{report_out}"
    );
}

/// The same case and rule change their verdict when `:asof` changes: with the
/// fact date unrecorded, no as-of date is unchecked, a date before the rule is
/// inapplicable, and a date inside the range is applicable.
#[test]
fn changing_asof_changes_the_verdict_and_the_conclusion() {
    let temp = TempRoot::new("asof-changes");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 起算 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 起算 甲
  source text "案件材料" locator "第一页"
rule 二〇二一年规则 :
  params x : 人
  premise 起算 x
  conclude 结论 x
  effective 2021-01-01
  source text "测试法" locator "第一条"
"#,
    );

    let plain = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 结论 甲".to_string(),
        ],
    );
    assert_exit(&plain, PROVED);
    let plain_out = stdout(&plain);
    assert!(
        plain_out.contains(
            "⟨二〇二一年规则⟩：适用性未判定（规则声明了生效区间，但未设置 :asof，案件事实也没有记录发生时间）"
        ),
        "{plain_out}"
    );

    let before = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2019-06-01".to_string(),
            ":why 结论 甲".to_string(),
        ],
    );
    assert_exit(&before, GAP);
    let before_out = stdout(&before);
    assert!(
        before_out.contains(
            "⟨二〇二一年规则⟩：不适用（案件日期 2019-06-01 早于规则生效日 2021-01-01，规则当时尚未生效）"
        ),
        "{before_out}"
    );

    let inside = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":why 结论 甲".to_string(),
        ],
    );
    assert_exit(&inside, PROVED);
    let inside_out = stdout(&inside);
    assert!(
        !inside_out.contains("时空适用性："),
        "the rule is applicable on this date:\n{inside_out}"
    );
}

/// A Henan case does not fire a rule recorded for Beijing only. The mismatch
/// is decided from `territory` and the fact's `occurred_in`, and it is shown
/// with the two codes.
#[test]
fn a_henan_case_does_not_fire_a_beijing_only_rule() {
    let temp = TempRoot::new("territory");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 行为 : 人 → Prop
pred 北京规则适用 : 人 → Prop
obj 甲 : 人
axiom 行为事实 : 行为 甲
  source text "案件材料" locator "第一页"
  occurred_in CN-HN
rule 北京规则 :
  params x : 人
  premise 行为 x
  conclude 北京规则适用 x
  jurisdiction CN
  territory CN-BJ
  source text "北京市条例" locator "第一条"
"#,
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":jurisdiction CN".to_string(),
            ":why 北京规则适用 甲".to_string(),
        ],
    );
    assert_exit(&output, GAP);
    let out = stdout(&output);
    assert!(
        out.contains("⟨北京规则⟩：不适用（规则地域 CN-BJ 与案件发生地 CN-HN 不同）"),
        "{out}"
    );

    let report = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":jurisdiction CN".to_string(),
            ":applicability 北京规则适用 甲".to_string(),
        ],
    );
    assert_exit(&report, PROVED);
    assert!(
        stdout(&report).contains("⟨北京规则⟩：不适用（规则地域 CN-BJ 与案件发生地 CN-HN 不同）"),
        "{}",
        stdout(&report)
    );
}

/// A repealed rule does not fire at a query date on or after its repeal day:
/// the conclusion disappears, the gap names the repeal, and `:applicability`
/// records the verdict.
#[test]
fn a_repealed_rule_does_not_silently_fire() {
    let temp = TempRoot::new("repealed");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 事实前提 : 人 → Prop
pred 处罚 : 人 → Prop
obj 甲 : 人
axiom 事实 : 事实前提 甲
  source text "案件材料" locator "第一页"
  occurred_at 2019-06-01
rule 旧规则 :
  params x : 人
  premise 事实前提 x
  conclude 处罚 x
  effective 2019-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#,
    );

    // Inside the range (the as-of date and the fact's date are both before the
    // repeal day): the rule applies.
    let inside = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2020-01-01".to_string(),
            ":why 处罚 甲".to_string(),
        ],
    );
    assert_exit(&inside, PROVED);
    assert!(
        !stdout(&inside).contains("时空适用性："),
        "{}",
        stdout(&inside)
    );

    // On the repeal day the rule is already out of force; no as-of date at
    // all also uses the fact's date and stays inside, so the change is the
    // session value.
    let repealed = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2021-01-01".to_string(),
            ":why 处罚 甲".to_string(),
        ],
    );
    assert_exit(&repealed, GAP);
    let repealed_out = stdout(&repealed);
    assert!(
        repealed_out.contains(
            "⟨旧规则⟩：不适用（案件日期 2021-01-01 已达到规则废止日 2021-01-01，规则已经失效）"
        ),
        "{repealed_out}"
    );

    let report = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2021-01-01".to_string(),
            ":applicability 处罚 甲".to_string(),
        ],
    );
    assert_exit(&report, PROVED);
    assert!(
        stdout(&report).contains("⟨旧规则⟩：不适用（案件日期 2021-01-01"),
        "{}",
        stdout(&report)
    );

    // Without a goal, `:applicability` lists every rule of the environment.
    let all = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2021-01-01".to_string(),
            ":applicability".to_string(),
        ],
    );
    assert_exit(&all, PROVED);
    let all_out = stdout(&all);
    assert!(
        all_out.contains("时空适用性（环境中 1 条规则）："),
        "{all_out}"
    );
    assert!(
        all_out.contains("⟨旧规则⟩：不适用（案件日期 2021-01-01"),
        "{all_out}"
    );
}

/// A conflict exists only between conclusions that both fired. When the
/// would-be other side is inapplicable, the conflict disappears for exactly
/// that reason: the excluded rule is no longer a side, and the remaining side
/// is proved.
#[test]
fn a_conflict_disappears_only_because_one_side_is_inapplicable() {
    let temp = TempRoot::new("conflict-applicability");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 前提一 : 人 → Prop
pred 前提二 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
obj 甲 : 人
contrary 批准 不批准
axiom 事实一 : 前提一 甲
  source text "案件材料" locator "第一页"
axiom 事实二 : 前提二 甲
  source text "案件材料" locator "第二页"
rule 旧规则 :
  params x : 人
  premise 前提一 x
  conclude 批准 x
  effective 2019-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
rule 新规则 :
  params x : 人
  premise 前提二 x
  conclude 不批准 x
  effective 2021-01-01
  source text "新法" locator "第一条"
"#,
    );

    // No as-of date: both rules fire (unchecked) and the contrary conclusions
    // stay unresolved, the old behaviour.
    let plain = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 批准 甲".to_string(),
        ],
    );
    assert_exit(&plain, GAP);
    let plain_out = stdout(&plain);
    assert!(plain_out.contains("冲突未决：批准 甲"), "{plain_out}");
    assert!(
        plain_out.contains(
            "⟨旧规则⟩：适用性未判定（规则声明了生效区间，但未设置 :asof，案件事实也没有记录发生时间）"
        ),
        "each conflict side labels its unchecked state:\n{plain_out}"
    );

    // A conflicted goal is not in the fact base, so its report comes from the
    // conflict's recorded rule witnesses.
    let plain_report = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":applicability 批准 甲".to_string(),
        ],
    );
    assert_exit(&plain_report, PROVED);
    let plain_report_out = stdout(&plain_report);
    assert!(
        plain_report_out.contains(
            "⟨旧规则⟩：适用性未判定（规则声明了生效区间，但未设置 :asof，案件事实也没有记录发生时间）"
        ),
        "{plain_report_out}"
    );
    assert!(
        plain_report_out.contains(
            "⟨新规则⟩：适用性未判定（规则声明了生效区间，但未设置 :asof，案件事实也没有记录发生时间）"
        ),
        "{plain_report_out}"
    );

    // At a date after the repeal the old rule is inapplicable, so it seeds no
    // conclusion and cannot be a conflict side.
    let dated = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":why 不批准 甲".to_string(),
        ],
    );
    assert_exit(&dated, PROVED);
    let dated_out = stdout(&dated);
    assert!(dated_out.contains("▸ 不批准 甲"), "{dated_out}");
    assert!(
        !dated_out.contains("冲突未决"),
        "the excluded rule is not a conflict side:\n{dated_out}"
    );
    let report = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":applicability 批准 甲".to_string(),
        ],
    );
    assert_exit(&report, PROVED);
    let report_out = stdout(&report);
    assert!(
        report_out.contains(
            "⟨旧规则⟩：不适用（案件日期 2022-01-01 已达到规则废止日 2021-01-01，规则已经失效）"
        ),
        "{report_out}"
    );
    let new_side = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":applicability 不批准 甲".to_string(),
        ],
    );
    assert_exit(&new_side, PROVED);
    assert!(
        stdout(&new_side).contains("⟨新规则⟩：适用"),
        "{}",
        stdout(&new_side)
    );
}

/// With two jurisdictions in the environment and no session choice, `:cert`
/// and `:why` refuse with exit 2 and list the codes sorted; `:gap` and
/// `:inspect` are not gated. Choosing a jurisdiction unblocks them.
#[test]
fn two_jurisdictions_require_an_explicit_choice() {
    let temp = TempRoot::new("gate");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
obj 甲 : 人
axiom 事实 : P 甲
  source text "案件材料" locator "第一页"

rule 日本规则 :
  params x : 人
  premise P x
  conclude R x
  jurisdiction JP
  source text "日本法" locator "第一条"

rule 中国规则 :
  params x : 人
  premise P x
  conclude Q x
  jurisdiction CN
  source text "中国法" locator "第一条"
"#,
    );
    let expected = "必须用 --jurisdiction 或 :jurisdiction 选择管辖：候选规则涉及 CN、JP";

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why Q 甲".to_string(),
        ],
    );
    assert_exit(&output, ERROR);
    assert!(
        stderr(&output).contains(expected),
        "the gate must name the sorted jurisdictions:\n{}",
        stderr(&output)
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":cert Q 甲".to_string(),
        ],
    );
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains(expected), "{}", stderr(&output));

    // `:gap` is not gated: it reports what is missing instead of choosing law.
    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":gap R 甲".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    assert!(
        stdout(&output).contains("目标可以推出"),
        "{}",
        stdout(&output)
    );

    // Choosing either jurisdiction lets the matching rule fire; the other
    // rule is inapplicable and is not needed for this goal.
    for (jurisdiction, goal) in [("CN", "Q 甲"), ("JP", "R 甲")] {
        let output = run_in(
            temp.root(),
            &[
                format!(":load {}", theory.display()),
                format!(":jurisdiction {jurisdiction}"),
                format!(":why {goal}"),
            ],
        );
        assert_exit(&output, PROVED);
        assert!(
            stdout(&output).contains("推导已通过独立校验"),
            "{jurisdiction}: {}",
            stdout(&output)
        );
    }
}

/// One jurisdiction in the environment never needs an explicit choice.
#[test]
fn a_single_jurisdiction_needs_no_choice() {
    let temp = TempRoot::new("single");
    let theory = temp.write("case.std", &scoped_theory());
    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 处罚 甲".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
}
