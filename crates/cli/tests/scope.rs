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

/// Remove every `applicability` member from a certificate JSON value, so two
/// certificates can be compared by their proof structure alone.
fn strip_applicability(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::Object(object) => {
            object.remove("applicability");
            for child in object.values_mut() {
                strip_applicability(child);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                strip_applicability(item);
            }
        }
        _ => {}
    }
}

fn line_containing<'a>(out: &'a str, needle: &str) -> &'a str {
    out.lines()
        .find(|line| line.contains(needle))
        .unwrap_or_else(|| panic!("no output line contains {needle:?}\n{out}"))
}

/// Remove the inline `〔verdict〕` segment from every line, so a test can
/// compare the derivation's structure independently of the applicability label.
fn strip_verdicts(block: &str) -> String {
    let mut stripped = String::new();
    for line in block.lines() {
        if let (Some(open), Some(close)) = (line.find('〔'), line.find('〕')) {
            if close > open {
                stripped.push_str(&line[..open]);
                stripped.push_str(&line[close + '〕'.len_utf8()..]);
                stripped.push('\n');
                continue;
            }
        }
        stripped.push_str(line);
        stripped.push('\n');
    }
    stripped
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

/// The event time is the reference: with no `:asof` the rule's recorded fact
/// keeps it inside its range and an unchecked jurisdiction verdict does not
/// block it (the conclusion, exit code and tree stay the old ones, and the
/// state is printed). A later `:asof` does not turn the old rule
/// inapplicable for an old event; the verdict and its basis are printed.
#[test]
fn event_time_drives_applicability_and_an_unchecked_rule_still_fires() {
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
            "⟨已废止规则⟩〔适用性未判定（规则声明了管辖，但会话未设置 :jurisdiction；已记录：事件时间 2020-05-06（区间内）；事件地点 CN-HN（覆盖））〕"
        ),
        "an unchecked judgement must be labelled with its evidence:\n{plain_out}"
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

    // A matching jurisdiction turns the same event into a positive judgement;
    // the event date, not the query date, is the reference.
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
        applicable_out.contains(
            "⟨已废止规则⟩〔适用（事件时间 2020-05-06（区间内）；事件地点 CN-HN（覆盖））〕"
        ),
        "an applicable verdict prints the covered event time and place:\n{applicable_out}"
    );
    assert_eq!(
        strip_verdicts(&tree(&plain_out)),
        strip_verdicts(&tree(&applicable_out)),
        "an applicable rule's derivation tree must be the old one"
    );

    // The query date is 2022, after the rule's repeal day, but the contract
    // was signed in 2020: the old rule still governs it.
    let later = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":jurisdiction CN".to_string(),
            ":why 处罚 甲".to_string(),
        ],
    );
    assert_exit(&later, PROVED);
    let later_out = stdout(&later);
    assert!(
        later_out.contains("⟨已废止规则⟩〔适用（事件时间 2020-05-06（区间内）"),
        "a later query date must not override an event time:\n{later_out}"
    );

    // `:applicability` shows the same verdict and its basis.
    let report = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":jurisdiction CN".to_string(),
            ":applicability 处罚 甲".to_string(),
        ],
    );
    assert_exit(&report, PROVED);
    assert!(
        stdout(&report).contains("⟨已废止规则⟩：适用（事件时间 2020-05-06（区间内）"),
        "{}",
        stdout(&report)
    );

    // `:cert` records the judgement and the session values by design; the
    // proof structure itself (assumptions, premises, root, conflicts) stays the
    // same once the applicability records are removed.
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
    let mut plain_nodes = plain_json["nodes"].clone();
    let mut dated_nodes = dated_json["nodes"].clone();
    strip_applicability(&mut plain_nodes);
    strip_applicability(&mut dated_nodes);
    assert_eq!(
        plain_nodes, dated_nodes,
        "an applicable date must not change the proof's nodes"
    );
    for field in ["assumptions", "root", "conflicts"] {
        assert_eq!(
            plain_json[field], dated_json[field],
            "an applicable date must not change the certificate's {field}"
        );
    }
    assert_eq!(
        plain_json["nodes"][1]["applicability"]["verdict"], "unchecked",
        "without a jurisdiction the rule is unchecked:\n{plain_json}"
    );
    assert_eq!(
        dated_json["nodes"][1]["applicability"]["verdict"], "applicable",
        "the event time is inside the range:\n{dated_json}"
    );
    assert!(
        dated_json["nodes"][1]["applicability"]["basis"]["session"]["as_of"].is_null(),
        "the event time, not :asof, is the reference:\n{dated_json}"
    );
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
            "⟨二〇二一年生效规则⟩：不适用（事件时间 2019-05-01 早于规则生效日 2021-01-01，规则当时尚未生效）"
        ),
        "{plain_out}"
    );

    // `:asof 2019-…` cannot override the recorded event time: the reference
    // stays 2019-05-01 and the rule is still inapplicable.
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
            "⟨二〇二一年生效规则⟩：不适用（事件时间 2019-05-01 早于规则生效日 2021-01-01，规则当时尚未生效）"
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
        later_out.contains("事件时间 2019-05-01 早于规则生效日 2021-01-01"),
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
            "时空适用性（目标：可撤销 甲）：\n  ⟨二〇二一年生效规则⟩：不适用（事件时间 2019-05-01"
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
            "⟨二〇二一年规则⟩〔适用性未判定（规则声明了生效区间，但实例引用的前提事实没有发生时间，会话也未设置 :asof）〕"
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
            "⟨二〇二一年规则⟩：不适用（事件时间 2019-06-01 早于规则生效日 2021-01-01，规则当时尚未生效）；依据：以查询基准日 2019-06-01 代替行为时（区间外）"
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
        inside_out
            .contains("⟨二〇二一年规则⟩〔适用（以查询基准日 2022-01-01 代替行为时（区间内））〕"),
        "the fallback date is labelled as a substitute for the event time:\n{inside_out}"
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
        out.contains("⟨北京规则⟩：不适用（规则地域 CN-BJ 不覆盖事件地点 CN-HN）"),
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
        stdout(&report).contains("⟨北京规则⟩：不适用（规则地域 CN-BJ 不覆盖事件地点 CN-HN）"),
        "{}",
        stdout(&report)
    );
}

/// A rule is inapplicable for an event that happened on or after its repeal
/// day, and the reason names the event time and the repeal day. The query
/// date is not what decides this.
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
  occurred_at 2022-01-01
rule 旧规则 :
  params x : 人
  premise 事实前提 x
  conclude 处罚 x
  effective 2019-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#,
    );

    // The event happened after the repeal: the rule never fires, whatever
    // the query date says.
    let repealed = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 处罚 甲".to_string(),
        ],
    );
    assert_exit(&repealed, GAP);
    let repealed_out = stdout(&repealed);
    assert!(
        repealed_out.contains(
            "⟨旧规则⟩：不适用（事件时间 2022-01-01 已达到规则废止日 2021-01-01，规则已经失效）"
        ),
        "{repealed_out}"
    );

    // `:applicability <goal>` reports the same verdict.
    let report = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":applicability 处罚 甲".to_string(),
        ],
    );
    assert_exit(&report, PROVED);
    assert!(
        stdout(&report).contains("⟨旧规则⟩：不适用（事件时间 2022-01-01"),
        "{}",
        stdout(&report)
    );

    // Without a goal, `:applicability` does not judge at all: it lists the
    // declaration's recorded scope and says an instance is needed.
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
        all_out.contains("时空适用性（未给定目标：不做判定，只列声明范围，共 1 条规则）："),
        "{all_out}"
    );
    assert!(
        all_out.contains("⟨旧规则⟩：〔生效 2019-01-01..2021-01-01（规则）〕"),
        "the declared scope is listed:\n{all_out}"
    );
    assert!(
        all_out.contains("未判定：需要目标命题或带发生时间/地点的事实。"),
        "{all_out}"
    );
    assert!(
        !all_out.contains("以查询基准日") && !all_out.contains("不适用（"),
        "no verdict may be invented without an instance:\n{all_out}"
    );
}

/// A contract signed in 2019 is governed by the law in force in 2019 even
/// when the query is made in 2026. The later rule must not reach back to the
/// earlier event, so the two rules never fire together.
#[test]
fn an_old_rule_governs_the_2019_contract_at_a_2026_asof() {
    let temp = TempRoot::new("no-retroactivity");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 合同签订 : 人 → Prop
pred 合同有效 : 人 → Prop
pred 合同无效 : 人 → Prop
obj 甲 : 人
contrary 合同有效 合同无效
axiom 签订 : 合同签订 甲
  source text "合同" locator "第一条"
  occurred_at 2019-05-01
rule 旧法 :
  params x : 人
  premise 合同签订 x
  conclude 合同有效 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
rule 新法 :
  params x : 人
  premise 合同签订 x
  conclude 合同无效 x
  effective 2021-01-01
  source text "新法" locator "第一条"
"#,
    );

    let old = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2026-01-01".to_string(),
            ":why 合同有效 甲".to_string(),
        ],
    );
    assert_exit(&old, PROVED);
    let old_out = stdout(&old);
    assert!(
        old_out.contains("⟨旧法⟩〔适用（事件时间 2019-05-01（区间内））〕"),
        "the old law covers the event time:\n{old_out}"
    );

    let new = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2026-01-01".to_string(),
            ":why 合同无效 甲".to_string(),
        ],
    );
    assert_exit(&new, GAP);
    let new_out = stdout(&new);
    assert!(
        new_out.contains(
            "⟨新法⟩：不适用（事件时间 2019-05-01 早于规则生效日 2021-01-01，规则当时尚未生效）"
        ),
        "the later law must not reach back:\n{new_out}"
    );
    assert!(
        !new_out.contains("冲突未决"),
        "only one side fired, so there is no conflict:\n{new_out}"
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
            "⟨旧规则⟩〔适用性未判定（规则声明了生效区间，但实例引用的前提事实没有发生时间，会话也未设置 :asof）〕"
        ),
        "each conflict side labels its unchecked state:\n{plain_out}"
    );
    assert!(
        plain_out.contains(
            "⟨新规则⟩〔适用性未判定（规则声明了生效区间，但实例引用的前提事实没有发生时间，会话也未设置 :asof）〕"
        ),
        "the other conflict side is labelled too:\n{plain_out}"
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
            "⟨旧规则⟩：适用性未判定（规则声明了生效区间，但实例引用的前提事实没有发生时间，会话也未设置 :asof）"
        ),
        "{plain_report_out}"
    );
    assert!(
        plain_report_out.contains(
            "⟨新规则⟩：适用性未判定（规则声明了生效区间，但实例引用的前提事实没有发生时间，会话也未设置 :asof）"
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
            "⟨旧规则⟩：不适用（事件时间 2022-01-01 已达到规则废止日 2021-01-01，规则已经失效）；依据：以查询基准日 2022-01-01 代替行为时（区间外）"
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
        stdout(&new_side)
            .contains("⟨新规则⟩：适用（以查询基准日 2022-01-01 代替行为时（区间内））"),
        "{}",
        stdout(&new_side)
    );
}

/// One premise event inside the range and another outside it is undecidable,
/// and an undecidable verdict does **not** fire: the partial evidence already
/// says the rule does not wholly govern this instance. The target is a gap and
/// the reason lists both dates; `:gap` also points at the missing explicit
/// reference time.
#[test]
fn partial_event_time_coverage_is_undecidable_and_does_not_fire() {
    let temp = TempRoot::new("partial-time");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 前期 : 人 → Prop
pred 后期 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 一 : 前期 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
axiom 二 : 后期 甲
  source text "材料" locator "二"
  occurred_at 2022-06-01
rule 跨期规则 :
  params x : 人
  premise 前期 x
  premise 后期 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#,
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2026-01-01".to_string(),
            ":why 结论 甲".to_string(),
        ],
    );
    assert_exit(&output, GAP);
    let out = stdout(&output);
    assert!(
        !out.contains("▸ 结论 甲"),
        "an undecidable verdict must not derive a conclusion:\n{out}"
    );
    assert!(
        out.contains(
            "⟨跨期规则⟩：适用性无法判定（事件时间 2019-05-01 在生效区间 1999-01-01..2021-01-01 内，2022-06-01 不在其中；部分覆盖不能当作适用）"
        ),
        "{out}"
    );

    // `:gap` lists the excluded candidate and tells the reader what would
    // unblock it (an explicit reference time, not implemented yet).
    let gap = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2026-01-01".to_string(),
            ":gap 结论 甲".to_string(),
        ],
    );
    assert_exit(&gap, GAP);
    let gap_out = stdout(&gap);
    assert!(
        gap_out.contains("候选 ⟨跨期规则⟩〔适用性无法判定（事件时间 2019-05-01"),
        "{gap_out}"
    );
    assert!(
        gap_out.contains("提示：需要为该争点显式指定引用时间（尚未实现）"),
        "{gap_out}"
    );

    let report = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":applicability 结论 甲".to_string(),
        ],
    );
    assert_exit(&report, PROVED);
    let report_out = stdout(&report);
    assert!(
        report_out.contains("2019-05-01") && report_out.contains("2022-06-01"),
        "both event times are listed:\n{report_out}"
    );
}

/// One premise event place covered by the territory and another not is
/// undecidable and does not fire; both places are listed and `:gap` points at
/// the missing explicit reference place.
#[test]
fn partial_event_place_coverage_is_undecidable_and_does_not_fire() {
    let temp = TempRoot::new("partial-place");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 河南事实 : 人 → Prop
pred 北京事实 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 一 : 河南事实 甲
  source text "材料" locator "一"
  occurred_in CN-HN
axiom 二 : 北京事实 甲
  source text "材料" locator "二"
  occurred_in CN-BJ
rule 河南规则 :
  params x : 人
  premise 河南事实 x
  premise 北京事实 x
  conclude 结论 x
  territory CN-HN
  source text "河南条例" locator "第一条"
"#,
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 结论 甲".to_string(),
        ],
    );
    assert_exit(&output, GAP);
    let out = stdout(&output);
    assert!(
        !out.contains("▸ 结论 甲"),
        "an undecidable verdict must not derive a conclusion:\n{out}"
    );
    assert!(
        out.contains(
            "⟨河南规则⟩：适用性无法判定（事件地点 CN-HN 在规则地域 CN-HN 内，CN-BJ 不在其中；部分覆盖不能当作适用）"
        ),
        "{out}"
    );

    let gap = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":gap 结论 甲".to_string(),
        ],
    );
    assert_exit(&gap, GAP);
    let gap_out = stdout(&gap);
    assert!(
        gap_out.contains("候选 ⟨河南规则⟩〔适用性无法判定（事件地点 CN-HN"),
        "{gap_out}"
    );
    assert!(
        gap_out.contains("提示：需要为该争点显式指定引用时间（尚未实现）"),
        "{gap_out}"
    );
}

/// `:issues` must judge each instance from the premise facts it actually holds.
/// The same fact set and the same instance must produce the same issue and the
/// same verdict whether `:asof` is inside or outside the rule's range.
#[test]
fn issues_judges_held_event_times_and_is_unchanged_by_asof() {
    let temp = TempRoot::new("issues-per-instance");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 前提甲 : 人 → Prop
pred 前提乙 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 一 : 前提甲 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
axiom 二 : 前提乙 甲
  source text "材料" locator "二"
  occurred_at 2021-01-01
rule 跨期规则 :
  params x : 人
  premise 前提甲 x
  premise 前提乙 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#,
    );

    let report = |out: &str| {
        let start = out
            .find("当前事实集下可争的结论")
            .unwrap_or_else(|| panic!("no issue scan:\n{out}"));
        out[start..].to_owned()
    };
    let mut scans = Vec::new();
    for as_of in ["2020-01-01", "2022-01-01"] {
        let output = run_in(
            temp.root(),
            &[
                format!(":load {}", theory.display()),
                format!(":asof {as_of}"),
                ":issues".to_string(),
            ],
        );
        assert_exit(&output, GAP);
        let out = stdout(&output);
        assert!(
            !out.contains("没有可争的结论"),
            "a partially covered rule is still a contestable issue with :asof {as_of}:\n{out}"
        );
        assert!(
            out.contains("跨期规则"),
            "the partially covered rule is listed with :asof {as_of}:\n{out}"
        );
        assert!(
            out.contains("2019-05-01") && out.contains("2021-01-01"),
            "the issue names the held event times with :asof {as_of}:\n{out}"
        );
        scans.push(report(&out));
    }
    assert_eq!(
        scans[0], scans[1],
        "the issue scan must not depend on :asof when event times are held"
    );
}

/// A held premise event inside the range plus one missing premise is still an
/// issue; the candidate's verdict is the one from the held fact, not `:asof`.
#[test]
fn issues_lists_an_issue_with_a_held_event_time_and_a_missing_premise() {
    let temp = TempRoot::new("issues-held-and-missing");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 前提 : 人 → Prop
pred 另一前提 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 前提 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
rule 规则 :
  params x : 人
  premise 前提 x
  premise 另一前提 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#,
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":asof 2022-01-01".to_string(),
            ":issues".to_string(),
        ],
    );
    assert_exit(&output, GAP);
    let out = stdout(&output);
    assert!(!out.contains("没有可争的结论"), "{out}");
    assert!(
        out.contains("候选 ⟨规则⟩〔适用（事件时间 2019-05-01（区间内））〕"),
        "the held fact decides the candidate verdict, not :asof:\n{out}"
    );
    assert!(
        out.contains("缺 ⟨另一前提 甲⟩"),
        "the missing premise is listed:\n{out}"
    );
    assert!(
        out.contains("判定口径：按已持有事实；补上缺失前提后判定可能变化。"),
        "the candidate verdict is labelled as a held-facts verdict:\n{out}"
    );
}

/// Two declarations of the same proposition with different event times are
/// two events for the instance consuming that proposition. Covering only one
/// is partial coverage, not a silent pick.
#[test]
fn two_facts_of_the_same_proposition_contribute_both_event_times() {
    let temp = TempRoot::new("same-proposition-dates");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 事件 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 记录一 : 事件 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
axiom 记录二 : 事件 甲
  source text "材料" locator "二"
  occurred_at 2022-06-01
rule 规则 :
  params x : 人
  premise 事件 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#,
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 结论 甲".to_string(),
        ],
    );
    assert_exit(&output, GAP);
    let out = stdout(&output);
    assert!(
        !out.contains("▸ 结论 甲"),
        "partial coverage must not fire:\n{out}"
    );
    assert!(
        out.contains("事件时间 2019-05-01")
            && out.contains("2022-06-01")
            && out.contains("部分覆盖不能当作适用"),
        "both recorded events are reported:\n{out}"
    );
}

/// An inapplicable rule must not act as a priority witness on the side of a
/// conflict: A applies and beats C, B is inapplicable, and C beats B. With B
/// correctly excluded A wins; if B were counted, the side would not uniformly
/// beat C and the conflict would stay unresolved.
#[test]
fn an_inapplicable_rule_is_not_a_conflict_or_priority_witness() {
    let temp = TempRoot::new("conflict-witness");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred 前提甲 : 人 → Prop
pred 前提乙 : 人 → Prop
pred 前提丙 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
obj 甲 : 人
contrary 批准 不批准
axiom 事实甲 : 前提甲 甲
  source text "材料" locator "甲"
  occurred_at 2019-05-01
axiom 事实乙 : 前提乙 甲
  source text "材料" locator "乙"
  occurred_at 2022-01-01
axiom 事实丙 : 前提丙 甲
  source text "材料" locator "丙"
  occurred_at 2019-05-01
rule A :
  params x : 人
  premise 前提甲 x
  conclude 批准 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "法A" locator "第一条"
rule B :
  params x : 人
  premise 前提乙 x
  conclude 批准 x
  effective 1999-01-01
  repealed 2021-01-01
  defeated_by C
  source text "法B" locator "第一条"
rule C :
  params x : 人
  premise 前提丙 x
  conclude 不批准 x
  effective 1999-01-01
  repealed 2021-01-01
  defeated_by A
  source text "法C" locator "第一条"
"#,
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why 批准 甲".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("▸ 批准 甲") && out.contains("冲突（已裁决）"),
        "A must win because the inapplicable B is not a witness:\n{out}"
    );
}

/// The certificate records the applicability verdict and its event time; a
/// fact date the environment registers differently from the certificate's
/// assumption is rejected instead of silently re-judged.
#[test]
fn the_certificate_records_the_verdict_and_rejects_a_changed_fact_date() {
    let temp = TempRoot::new("cert-applicability");
    let source = r#"
sort 人
pred 行为 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 事实 : 行为 甲
  source text "材料" locator "一"
  occurred_at 2019-05-01
rule 规则 :
  params x : 人
  premise 行为 x
  conclude 结论 x
  effective 1999-01-01
  repealed 2021-01-01
  source text "旧法" locator "第一条"
"#;
    let theory = temp.write("case.std", source);

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":cert 结论 甲".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let json = &out[out.find('{').expect("the certificate JSON starts")..];
    let value: serde_json::Value = serde_json::from_str(json).expect("the certificate is JSON");
    assert_eq!(value["format_version"], 8);
    let record = &value["nodes"][1]["applicability"];
    assert_eq!(record["verdict"], "applicable");
    assert_eq!(
        record["basis"]["dates"][0]["date"], "2019-05-01",
        "the event time is recorded:\n{json}"
    );
    assert_eq!(record["basis"]["dates"][0]["query_date_fallback"], false);
    assert!(record["basis"]["session"]["as_of"].is_null());
    assert_eq!(
        record["basis"]["scope"]["effective_from"], "1999-01-01",
        "the rule's declared range is quoted:\n{json}"
    );
    let cert_path = temp.write("cert.json", json);

    // The environment now registers a different occurred_at for the same
    // fact. The certificate's assumption and reference date no longer match
    // it, so the logical check must fail rather than re-judge and pass.
    let changed = source.replace("occurred_at 2019-05-01", "occurred_at 2022-06-01");
    temp.write("case.std", &changed);
    let verify = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            format!(":verify-cert {}", cert_path.display()),
        ],
    );
    assert_exit(&verify, ERROR);
    let verify_out = stdout(&verify);
    assert!(verify_out.contains("环境校验：通过"), "{verify_out}");
    assert!(verify_out.contains("逻辑校验：失败"), "{verify_out}");
    assert!(
        !verify_out.contains("内核证明：通过"),
        "no kernel layer may pass after a failed logical check:\n{verify_out}"
    );
    let err = stderr(&verify);
    assert!(err.contains("假设") && err.contains("事件时间"), "{err}");
}

/// Without a goal, `:applicability` lists declarations and does not saturate:
/// an oscillating theory is a report, not an error.
#[test]
fn applicability_without_a_goal_does_not_saturate_or_judge() {
    let temp = TempRoot::new("applicability-no-saturate");
    let theory = temp.write(
        "case.std",
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
obj 甲 : 人
axiom 种子 : P 甲
  source text "材料" locator "一"
rule 规则一 :
  params x : 人
  premise P x
  conclude Q x
  unless Q x
  source text "法一" locator "第一条"
rule 规则二 :
  params x : 人
  premise Q x
  conclude P x
  unless P x
  source text "法二" locator "第二条"
"#,
    );

    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":applicability".to_string(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("未判定：需要目标命题或带发生时间/地点的事实。"),
        "{out}"
    );
    assert!(
        !out.contains("不适用（") && !out.contains("以查询基准日"),
        "the no-goal report must not invent a verdict:\n{out}"
    );

    // The oscillation is still an error when a goal is actually queried.
    let why = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":why Q 甲".to_string(),
        ],
    );
    assert_exit(&why, ERROR);
    assert!(stderr(&why).contains("振荡"), "{}", stderr(&why));
}

/// With two jurisdictions in the environment and no session choice, `:cert`,
/// `:why` and `:explain` refuse with exit 2 and list the codes sorted; `:gap`
/// and `:inspect` are not gated. Choosing a jurisdiction unblocks them.
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

    // `:explain` uses the same certificate and checks, so the same ambiguity
    // gate applies; the README promises the same exit codes as `:why`.
    let output = run_in(
        temp.root(),
        &[
            format!(":load {}", theory.display()),
            ":explain Q 甲".to_string(),
        ],
    );
    assert_exit(&output, ERROR);
    assert!(
        stderr(&output).contains(expected),
        ":explain must be gated like :why:\n{}",
        stderr(&output)
    );

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
