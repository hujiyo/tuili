//! End-to-end tests for `carry_occurrence` and the `within` code hierarchy.
//!
//! The `carry_occurrence` group pins the declared event-time/place propagation
//! along a rule chain: the third step is judged by the inherited time, the
//! provenance is named in the basis text, the clause is off by default
//! (existing behaviour unchanged), propagation stops at a rule without it, and
//! multiple witnesses are unioned and re-checkable from the certificate.
//!
//! The `within` group pins the declared code hierarchy: a parent rule covers a
//! child fact, a child rule does not cover a parent fact, an undeclared prefix
//! pair stays undecidable, the two dimensions stay independent, load-time
//! validation rejects reflexive/duplicate/cyclic declarations, and removing the
//! declaration makes the old certificate fail its logical recheck.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP: i32 = 1;
const ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn example(name: &str) -> String {
    repo_root()
        .join("examples")
        .join(name)
        .to_string_lossy()
        .into_owned()
}

fn run(commands: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(commands)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn session(theory: &str, commands: &[&str]) -> Output {
    let mut args = vec![format!(":load {theory}")];
    args.extend(commands.iter().map(|command| command.to_string()));
    run(&args)
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

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

fn line_containing<'a>(out: &'a str, needle: &str) -> &'a str {
    out.lines()
        .find(|line| line.contains(needle))
        .unwrap_or_else(|| panic!("no output line contains {needle:?}\n{out}"))
}

/// A temporary `.std` theory and certificate file, removed when the test ends.
struct TempFile {
    path: PathBuf,
}

impl TempFile {
    fn theory(tag: &str, source: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-carry-within-{}-{tag}-{n}.std",
            std::process::id()
        ));
        fs::write(&path, source).unwrap_or_else(|error| panic!("write theory: {error}"));
        TempFile { path }
    }

    fn certificate(tag: &str, out: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-carry-within-{}-{tag}-{n}.json",
            std::process::id()
        ));
        let start = out
            .find('{')
            .unwrap_or_else(|| panic!("no certificate JSON:\n{out}"));
        fs::write(&path, &out[start..]).unwrap_or_else(|error| panic!("write cert: {error}"));
        TempFile { path }
    }

    fn path(&self) -> String {
        self.path.to_string_lossy().into_owned()
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

/// The three-step chain used by the carry tests: only the bottom fact records
/// 2019-05-01; `carry` decides whether the upper steps inherit it.
fn chain_source(carry_a: bool, carry_b: bool, carry_c: bool) -> String {
    let clause = |carry: bool| {
        if carry {
            "  carry_occurrence\n"
        } else {
            ""
        }
    };
    format!(
        "sort 人\n\
         pred 行为 : 人 → Prop\n\
         pred 义务 : 人 → Prop\n\
         pred 中间 : 人 → Prop\n\
         pred 责任 : 人 → Prop\n\
         obj 甲 : 人\n\
         axiom 甲行为 : 行为 甲\n\
         \x20 occurred_at 2019-05-01\n\
         \x20 source text \"示例卷宗\" locator \"行为\"\n\
         rule 规则A :\n\
         \x20 params p : 人\n\
         \x20 premise 行为 p\n\
         \x20 conclude 义务 p\n\
         {a}\
         \x20 effective 2018-01-01\n\
         \x20 repealed 2020-01-01\n\
         \x20 source text \"示例法\" locator \"A\"\n\
         rule 规则B :\n\
         \x20 params p : 人\n\
         \x20 premise 义务 p\n\
         \x20 conclude 中间 p\n\
         {b}\
         \x20 effective 2018-01-01\n\
         \x20 repealed 2020-01-01\n\
         \x20 source text \"示例法\" locator \"B\"\n\
         rule 规则C :\n\
         \x20 params p : 人\n\
         \x20 premise 中间 p\n\
         \x20 conclude 责任 p\n\
         {c}\
         \x20 effective 2018-01-01\n\
         \x20 repealed 2020-01-01\n\
         \x20 source text \"示例法\" locator \"C\"\n",
        a = clause(carry_a),
        b = clause(carry_b),
        c = clause(carry_c),
    )
}

#[test]
fn carry_occurrence_judges_the_third_step_by_the_inherited_event_time() {
    let theory = TempFile::theory("chain", &chain_source(true, true, true));
    let output = session(&theory.path(), &[":why 责任 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let conclusion = line_containing(&out, "▸ 责任 甲");
    assert!(
        conclusion.contains("适用（事件时间 2019-05-01（区间内"),
        "the third step must be judged by the inherited 2019 event time: {conclusion}"
    );
    assert!(
        conclusion.contains("继承自前提「中间 甲」"),
        "the basis must name the step the inherited time came from: {conclusion}"
    );
    assert!(
        conclusion.contains("规则 ⟨规则B⟩"),
        "the basis must name the rule that derived the premise: {conclusion}"
    );
    assert!(out.contains("推导已通过独立校验"), "{out}");
}

#[test]
fn without_carry_occurrence_the_chain_behaves_exactly_as_before() {
    let theory = TempFile::theory("nocarry", &chain_source(false, false, false));
    let output = session(&theory.path(), &[":why 责任 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let conclusion = line_containing(&out, "▸ 责任 甲");
    assert!(
        conclusion.contains("适用性未判定（规则声明了生效区间"),
        "without the clause the conclusion has no event time: {conclusion}"
    );
    assert!(
        !out.contains("继承自前提"),
        "an undeclared rule must not inherit anything: {out}"
    );
}

#[test]
fn carry_stops_at_a_rule_that_does_not_declare_it() {
    // A and C carry, B does not: the 2019 time reaches 义务 but not 中间, so
    // C falls back to the session date rather than inheriting 2019.
    let theory = TempFile::theory("stop", &chain_source(true, false, true));
    let output = session(&theory.path(), &[":asof 2019-06-01", ":why 责任 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let conclusion = line_containing(&out, "▸ 责任 甲");
    assert!(
        conclusion.contains("以查询基准日 2019-06-01 代替行为时"),
        "a broken chain falls back to :asof: {conclusion}"
    );
    assert!(
        !conclusion.contains("继承自前提"),
        "propagation must stop at the rule without the clause: {conclusion}"
    );
}

#[test]
fn multiple_carry_witnesses_union_their_event_times_and_recheck() {
    let source = "\
sort 人
pred 行为一 : 人 → Prop
pred 行为二 : 人 → Prop
pred 义务 : 人 → Prop
pred 责任 : 人 → Prop
obj 甲 : 人
axiom 甲行为一 : 行为一 甲
  occurred_at 2019-05-01
  source text \"示例卷宗\" locator \"一\"
axiom 甲行为二 : 行为二 甲
  occurred_at 2020-05-01
  source text \"示例卷宗\" locator \"二\"
rule 规则一 :
  params p : 人
  premise 行为一 p
  conclude 义务 p
  carry_occurrence
  source text \"示例法\" locator \"一\"
rule 规则二 :
  params p : 人
  premise 行为二 p
  conclude 义务 p
  carry_occurrence
  source text \"示例法\" locator \"二\"
rule 规则三 :
  params p : 人
  premise 义务 p
  conclude 责任 p
  carry_occurrence
  effective 2018-01-01
  repealed 2021-01-01
  source text \"示例法\" locator \"三\"
";
    let theory = TempFile::theory("multi", source);
    let output = session(&theory.path(), &[":why 责任 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let conclusion = line_containing(&out, "▸ 责任 甲");
    assert!(
        conclusion.contains("事件时间 2019-05-01") && conclusion.contains("事件时间 2020-05-01"),
        "the inherited set is the union over both witnesses: {conclusion}"
    );
    assert!(
        conclusion.contains("规则 ⟨规则一⟩、⟨规则二⟩"),
        "the basis names both deriving rules: {conclusion}"
    );

    let cert_output = session(&theory.path(), &[":cert 责任 甲"]);
    assert_exit(&cert_output, PROVED);
    let certificate = TempFile::certificate("multi", &stdout(&cert_output));
    let verified = run(&[
        format!(":load {}", theory.path()),
        format!(":verify-cert \"{}\" 责任 甲", certificate.path()),
    ]);
    assert_exit(&verified, PROVED);
    assert!(
        stdout(&verified).contains("逻辑校验：通过"),
        "the checker must rebuild the inherited dates from the recorded witnesses: {}",
        stdout(&verified)
    );
}

#[test]
fn a_parent_territory_rule_covers_a_child_fact_and_names_the_chain() {
    let theory = example("地域层级-省与国.std");
    let output = session(&theory, &[":jurisdiction CN-HN", ":why 应适用 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("事件地点 CN-HN（覆盖：依据层级 CN-HN ⊂ CN 落入规则范围）"),
        "the basis must name the declared hierarchy: {out}"
    );
    assert!(
        out.contains("案件管辖 CN-HN（依据层级 CN-HN ⊂ CN 落入规则范围）"),
        "the jurisdiction dimension must use its own declared chain: {out}"
    );
}

#[test]
fn a_child_territory_rule_does_not_cover_a_parent_fact() {
    let theory = example("地域层级-省与国.std");
    let output = session(&theory, &[":jurisdiction CN-HN", ":gap 省级规定 乙"]);
    assert_exit(&output, GAP);
    let out = stdout(&output);
    let candidate = line_containing(&out, "候选 ⟨省级规则⟩");
    assert!(
        candidate.contains("不适用"),
        "the child rule must not cover the parent event: {candidate}"
    );
    assert!(
        candidate.contains("规则地域 CN-HN 是事件地点 CN 的子区域"),
        "the basis must say why the rule does not reach the parent code: {candidate}"
    );
}

#[test]
fn a_jurisdiction_hierarchy_uses_its_own_dimension_only() {
    let theory = example("地域层级-省与国.std");
    // The case's legal system is CN-HN; the national rule declares CN and the
    // jurisdiction chain makes it cover the case, while the territory chain
    // alone would not relate the jurisdiction codes.
    let output = session(&theory, &[":jurisdiction CN-HN", ":why 应适用 甲"]);
    assert_exit(&output, PROVED);
    assert!(
        stdout(&output).contains("依据层级 CN-HN ⊂ CN 落入规则范围"),
        "{}",
        stdout(&output)
    );
}

#[test]
fn an_undeclared_hierarchy_stays_undecidable() {
    let source = "\
sort 人
pred 行为 : 人 → Prop
pred 省规 : 人 → Prop
obj 乙 : 人
axiom 乙行为 : 行为 乙
  occurred_at 2019-05-01
  occurred_in CN
  source text \"示例卷宗\" locator \"乙\"
rule 省级规则 :
  params p : 人
  premise 行为 p
  conclude 省规 p
  effective 2018-01-01
  territory CN-HN
  source text \"示例法\" locator \"省级规则\"
";
    let theory = TempFile::theory("no-within", source);
    let output = session(&theory.path(), &[":gap 省规 乙"]);
    assert_exit(&output, GAP);
    let out = stdout(&output);
    let candidate = line_containing(&out, "候选 ⟨省级规则⟩");
    assert!(
        candidate.contains("无法判定") && candidate.contains("上下位关系但未声明层级"),
        "an undeclared prefix pair must stay undecidable: {candidate}"
    );
}

#[test]
fn reflexive_duplicate_and_cyclic_within_declarations_are_load_errors() {
    for (tag, lines, needle) in [
        ("self", "territory CN within CN", "自反的层级声明没有意义"),
        (
            "duplicate",
            "territory CN-HN within CN\nterritory CN-HN within CN",
            "这一条已经声明过了",
        ),
        (
            "cycle",
            "territory CN-HN within CN\nterritory CN within CN-HN",
            "形成环",
        ),
    ] {
        let theory = TempFile::theory(tag, &format!("sort 人\n{lines}\n"));
        let output = session(&theory.path(), &[]);
        assert_exit(&output, ERROR);
        let err = stderr(&output);
        assert!(
            err.contains(needle),
            "{tag}: expected {needle:?} in:\n{err}"
        );
    }
}

#[test]
fn removing_the_within_declaration_invalidates_the_old_certificate() {
    let theory = example("地域层级-省与国.std");
    let output = session(&theory, &[":jurisdiction CN-HN", ":cert 应适用 甲"]);
    assert_exit(&output, PROVED);
    let certificate = TempFile::certificate("hierarchy", &stdout(&output));
    let verified = run(&[
        format!(":load {theory}"),
        ":jurisdiction CN-HN".to_owned(),
        format!(":verify-cert \"{}\" 应适用 甲", certificate.path()),
    ]);
    assert_exit(&verified, PROVED);
    assert!(
        stdout(&verified).contains("逻辑校验：通过"),
        "{}",
        stdout(&verified)
    );

    let stripped: String = fs::read_to_string(&theory)
        .expect("read example")
        .lines()
        .filter(|line| !line.contains("within"))
        .collect::<Vec<_>>()
        .join("\n");
    let stripped = TempFile::theory("stripped", &stripped);
    let rejected = run(&[
        format!(":load {}", stripped.path()),
        ":jurisdiction CN-HN".to_owned(),
        format!(":verify-cert \"{}\" 应适用 甲", certificate.path()),
    ]);
    assert_exit(&rejected, ERROR);
    let err = stderr(&rejected);
    assert!(
        err.contains("依赖当前环境未声明的层级"),
        "the failure must say the recorded basis depends on a missing declaration: {err}"
    );
    assert!(
        err.contains("节点"),
        "the failure must name the node it rejected: {err}"
    );
}

#[test]
fn a_within_declaration_after_a_rule_is_a_top_level_item() {
    let source = "\
sort 人
pred 行为 : 人 → Prop
pred 应适用 : 人 → Prop
obj 甲 : 人
axiom 甲行为 : 行为 甲
  occurred_at 2019-05-01
  occurred_in CN-HN
  source text \"示例卷宗\" locator \"甲\"
rule 国家规则 :
  params p : 人
  premise 行为 p
  conclude 应适用 p
  effective 2018-01-01
  territory CN
  source text \"示例法\" locator \"国家规则\"
territory CN-HN within CN
";
    let theory = TempFile::theory("after-rule", source);
    let output = session(&theory.path(), &[":why 应适用 甲"]);
    assert_exit(&output, PROVED);
    assert!(
        stdout(&output).contains("依据层级 CN-HN ⊂ CN 落入规则范围"),
        "a hierarchy declaration after a rule body starts a new item: {}",
        stdout(&output)
    );
}

#[test]
fn the_carry_occurrence_clause_is_line_oriented_and_single() {
    for (tag, line, needle) in [
        (
            "inline",
            "premise 行为 p\n  conclude 义务 p carry_occurrence",
            "carry_occurrence",
        ),
        (
            "repeat",
            "conclude 义务 p\n  carry_occurrence\n  carry_occurrence",
            "carry_occurrence 重复声明",
        ),
    ] {
        let source = format!(
            "sort 人\n\
             pred 行为 : 人 → Prop\n\
             pred 义务 : 人 → Prop\n\
             obj 甲 : 人\n\
             axiom 甲行为 : 行为 甲\n\
             \x20 source text \"示例卷宗\" locator \"行为\"\n\
             rule 规则A :\n\
             \x20 params p : 人\n\
             {line}\n\
             \x20 source text \"示例法\" locator \"A\"\n"
        );
        let theory = TempFile::theory(tag, &source);
        let output = session(&theory.path(), &[]);
        assert_exit(&output, ERROR);
        let err = stderr(&output);
        assert!(
            err.contains(needle),
            "{tag}: expected {needle:?} in:\n{err}"
        );
    }
}

#[test]
fn carry_occurrence_combines_with_a_guard_and_an_unless() {
    let source = "\
sort 人
pred 行为 : 人 → Prop
pred 义务 : 人 → Prop
pred 责任 : 人 → Prop
pred 阻断 : 人 → Prop
obj 甲 : 人
axiom 甲行为 : 行为 甲
  occurred_at 2019-05-01
  source text \"示例卷宗\" locator \"行为\"
rule 规则A :
  params p : 人
  premise 行为 p
  conclude 义务 p
  carry_occurrence
  source text \"示例法\" locator \"A\"
rule 规则B :
  params p : 人
  premise 义务 p
  conclude 责任 p
  carry_occurrence
  guard (le 2019 2019)
  unless 阻断 p
  effective 2018-01-01
  repealed 2020-01-01
  source text \"示例法\" locator \"B\"
";
    let theory = TempFile::theory("guard", source);
    let output = session(&theory.path(), &[":why 责任 甲"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let conclusion = line_containing(&out, "▸ 责任 甲");
    assert!(
        conclusion.contains("事件时间 2019-05-01") && conclusion.contains("继承自前提「义务 甲」"),
        "{conclusion}"
    );
    assert!(out.contains("推导已通过独立校验"), "{out}");
}
