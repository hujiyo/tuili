//! End-to-end tests for `revision`: rules that are historical versions of one
//! provision.
//!
//! The group is a declared relation, never an inference. What the tests pin:
//!
//! * the applicability judgement still decides which version covers an
//!   instance, so a time point covered by only one version proves through that
//!   version and the other version is reported as inapplicable in the gap;
//! * an instance covered by both versions is a normal unresolved conflict when
//!   no priority is declared, and the reason names the historical-version
//!   group instead of leaving a bare "no priority";
//! * a priority edge with a source decides the conflict: the winner is fixed,
//!   the basis and its sources enter the certificate, and `:verify-cert`
//!   accepts it;
//! * the loader refuses a lone `revision`, a reused rule name inside a group, a
//!   version without an effective range, and an identifier that names an
//!   existing declaration.
//!
//! The system never selects the newer or the older version and never compares
//! their severity: that is a legal judgement, declared by the priority edge.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

/// A proved root with no unresolved obligation.
const PROVED: i32 = 0;
/// A gap, an unresolved conflict, or a root with an unresolved obligation.
const GAP_OR_CONFLICT: i32 = 1;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn example(name: &str) -> String {
    let path = repo_root().join("examples").join(name);
    assert!(path.is_file(), "missing example file: {}", path.display());
    path.to_string_lossy().into_owned()
}

/// Run the CLI from the repository root without the default pack environment,
/// so the output contains only what the example itself declares.
fn run(commands: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .arg("--no-default-packs")
        .args(commands)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn session(name: &str, commands: &[&str]) -> Output {
    let mut all = vec![format!(":load {}", example(name))];
    all.extend(commands.iter().map(|command| command.to_string()));
    run(all)
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
            "std-deduce-cli-{}-{tag}-{n}.std",
            std::process::id()
        ));
        fs::write(&path, source)
            .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        TempTheory { path }
    }
}

impl Drop for TempTheory {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn check(output: &Output, expected: i32, needles: &[&str]) {
    let code = output.status.code();
    let out = stdout(output);
    let err = stderr(output);
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

/// Assert the exit code and that stderr (the batch entry's diagnostic channel)
/// contains every needle.
fn check_stderr(output: &Output, expected: i32, needles: &[&str]) {
    let code = output.status.code();
    let out = stdout(output);
    let err = stderr(output);
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    for needle in needles {
        assert!(
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
}

/// A theory with two versions of one provision (`第二十条`), each with its own
/// effective range. `old_effective` / `new_effective` let a test omit a version's
/// interval or reuse a name.
fn two_versions(
    old_name: &str,
    new_name: &str,
    old_effective: &str,
    new_effective: &str,
) -> String {
    let interval = |effective: &str| {
        if effective.is_empty() {
            String::new()
        } else {
            format!("  effective {effective}\n")
        }
    };
    format!(
        "sort 人\n\
         sort 法条\n\
         pred 行为 : 人 → Prop\n\
         pred 应适用 : 法条 → 人 → Prop\n\
         obj 甲 : 人\n\
         obj 旧版 : 法条\n\
         obj 新版 : 法条\n\
         axiom 事 : 行为 甲\n  source text \"示例卷宗\" locator \"行为\"\n\
         rule {old_name} :\n  params p : 人\n  premise 行为 p\n  conclude 应适用 旧版 p\n\
         {}  revision 第二十条\n  source text \"示例刑法\" locator \"第二十条（旧版）\"\n\
         rule {new_name} :\n  params p : 人\n  premise 行为 p\n  conclude 应适用 新版 p\n\
         {}  revision 第二十条\n  source text \"示例刑法\" locator \"第二十条（新版）\"\n",
        interval(old_effective),
        interval(new_effective),
    )
}

/// `:inspect` shows the declared group on each version and nothing on a rule
/// outside a group.
#[test]
fn inspect_shows_the_revision_group_on_every_version() {
    let output = session("历史版本-新旧法.std", &[":inspect"]);
    let out = stdout(&output);
    let marked = out
        .lines()
        .filter(|line| line.contains("〔历史版本 第二十条〕"))
        .count();
    assert_eq!(marked, 2, "both versions must show the group\n{out}");
    // The group is displayed next to the rule that wrote the clause; the
    // identifier is not invented from the rule name or the provision number.
    assert!(out.contains("rule  旧版规则"), "{out}");
    assert!(out.contains("rule  新版规则"), "{out}");
}

/// Time point 1 (2019-05-01): only the old version covers the event, so the old
/// version fires and the new version is inapplicable.
#[test]
fn the_old_version_fires_at_a_time_point_it_alone_covers() {
    let output = session("历史版本-新旧法.std", &[":why 应适用 旧版 甲"]);
    // The time point 3 conflict involves the same rules, so the certificate
    // reports it as a related unresolved conflict: honesty over a clean exit
    // code. The old version's own instance is applicable and proved.
    check(
        &output,
        GAP_OR_CONFLICT,
        &[
            "▸ 应适用 旧版 甲  ⟨旧版规则⟩〔适用（事件时间 2019-05-01（区间内））〕",
            "实例：p ↦ 甲",
        ],
    );
    let gap = session("历史版本-新旧法.std", &[":gap 应适用 新版 甲"]);
    check(
        &gap,
        GAP_OR_CONFLICT,
        &[
            "候选 ⟨新版规则⟩〔不适用（事件时间 2019-05-01 早于规则生效日 2021-01-01",
            "规则当时尚未生效",
        ],
    );
}

/// Time point 2 (2023-02-01): only the new version covers the event, so the new
/// version fires and the old version is inapplicable because it was repealed.
#[test]
fn the_new_version_fires_at_a_time_point_the_old_version_no_longer_covers() {
    let output = session("历史版本-新旧法.std", &[":why 应适用 新版 丙"]);
    check(
        &output,
        GAP_OR_CONFLICT,
        &[
            "▸ 应适用 新版 丙  ⟨新版规则⟩〔适用（事件时间 2023-02-01（区间内））〕",
            "实例：p ↦ 丙",
        ],
    );
    let gap = session("历史版本-新旧法.std", &[":gap 应适用 旧版 丙"]);
    check(
        &gap,
        GAP_OR_CONFLICT,
        &[
            "候选 ⟨旧版规则⟩〔不适用（事件时间 2023-02-01 已达到规则废止日 2022-01-01",
            "规则已经失效",
        ],
    );
}

/// Time point 3 (2021-06-01): both versions cover the event. Without a declared
/// priority the conflict is unresolved and the reason names the two historical
/// versions; neither conclusion enters the fact base and both derivations are
/// printed.
#[test]
fn both_versions_at_the_overlap_are_an_unresolved_historical_conflict() {
    let output = session("历史版本-新旧法.std", &[":why 应适用 旧版 乙"]);
    check(
        &output,
        GAP_OR_CONFLICT,
        &[
            "冲突未决：应适用 旧版 乙",
            "原因：两侧规则之间没有声明任何优先关系",
            "两侧是同一法条的两个历史版本（revision 组 `第二十条`），没有声明哪一版优先",
            "系统不自动选新法或旧法，也不自动判断哪一版更轻",
            "── 冲突左方：应适用 新版 乙 ──",
            "── 冲突右方：应适用 旧版 乙 ──",
        ],
    );
    // `:gap` on a conflicted target takes the unresolved-conflict report and
    // names the same relation; the note is produced by the same code as `:why`.
    let gap = session("历史版本-新旧法.std", &[":gap 应适用 旧版 乙"]);
    check(
        &gap,
        GAP_OR_CONFLICT,
        &[
            "冲突未决：应适用 旧版 乙",
            "历史版本：两侧是同一法条的两个历史版本（revision 组 `第二十条`）",
        ],
    );
}

/// A downstream rule whose premise is a version conflict gets the same naming
/// in the nested gap body, not only at the root.
#[test]
fn a_nested_gap_names_the_historical_versions() {
    let src = format!(
        "{}\
         pred 处罚 : 人 → Prop\n\
         rule 处罚规则 :\n  params p : 人\n  premise 应适用 旧版 p\n  conclude 处罚 p\n  \
         source text \"示例刑法\" locator \"第二十条（法律后果）\"\n",
        two_versions("旧版规则", "新版规则", "1999-01-01", "2021-01-01").replace(
            "pred 应适用 : 法条 → 人 → Prop\n",
            "pred 应适用 : 法条 → 人 → Prop\nunique 应适用 1\n"
        ),
    );
    let theory = TempTheory::new("nested", &src);
    let output = run(vec![
        theory.path.display().to_string(),
        ":gap 处罚 甲".to_owned(),
    ]);
    check(
        &output,
        GAP_OR_CONFLICT,
        &[
            "缺 ⟨应适用 旧版 甲⟩",
            "目标处于冲突中：未决的结论不进入事实库，需要人工裁决。",
            "历史版本：两侧是同一法条的两个历史版本（revision 组 `第二十条`）",
        ],
    );
}

/// The unresolved-conflict obligation in the certificate names the group too:
/// the certificate keeps the v11 shape, only the human-readable description
/// gains the relation.
#[test]
fn the_certificate_names_the_historical_versions_in_the_obligation() {
    let output = session("历史版本-新旧法.std", &[":cert 应适用 旧版 乙"]);
    check(&output, GAP_OR_CONFLICT, &["open_obligations", "历史版本"]);
    let out = stdout(&output);
    let json_start = out.find('{').expect("the certificate JSON starts");
    let certificate: serde_json::Value =
        serde_json::from_str(&out[json_start..]).expect("the certificate is JSON");
    // No new field: the v11 shape is unchanged and the reason is recorded as
    // `no_priority`; only its description mentions the versions.
    assert_eq!(
        certificate["format_version"],
        serde_json::Value::from(11),
        "{certificate}"
    );
    let obligations = certificate["open_obligations"]
        .as_array()
        .expect("open_obligations is an array");
    let conflict = obligations
        .iter()
        .find(|obligation| obligation["kind"] == "unresolved_conflict")
        .unwrap_or_else(|| panic!("no unresolved_conflict obligation: {certificate}"));
    let description = conflict["description"]
        .as_str()
        .expect("the description is a string");
    assert!(
        description.contains("两个历史版本") && description.contains("第二十条"),
        "{description}"
    );
}

/// With an explicit priority edge the same overlap is decided: the old version
/// wins, the basis (the edge, its declaring namespace and its sources) is
/// printed and recorded, and the certificate verifies.
#[test]
fn a_declared_priority_edge_decides_the_historical_conflict() {
    let goal = "example.revision.应适用 example.revision.旧版 example.revision.乙";
    let output = session("历史版本-从旧兼从轻.std", &[&format!(":why {goal}")]);
    check(
        &output,
        PROVED,
        &[
            "冲突（已裁决）：example.revision.应适用 example.revision.新版 example.revision.乙",
            "依据：example.revision 的 priority example.revision.旧版规则 over example.revision.新版规则",
            "出处：示例刑法 第二十条第三项（从旧兼从轻）",
            "推导已通过独立校验。",
        ],
    );
    // The group is still recorded on the rules; the priority is the only thing
    // that decides, and it is declared by the module, not inferred.
    let inspect = session("历史版本-从旧兼从轻.std", &[":inspect"]);
    let out = stdout(&inspect);
    assert!(
        out.contains("〔历史版本 第二十条〕 [example.revision]"),
        "{out}"
    );
}

/// The decision is written into the v11 certificate as a defeated conflict with
/// a priority basis, and `:verify-cert` accepts it.
#[test]
fn the_priority_certificate_records_and_verifies_the_edge() {
    let goal = "example.revision.应适用 example.revision.旧版 example.revision.乙";
    let output = session("历史版本-从旧兼从轻.std", &[&format!(":cert {goal}")]);
    assert_eq!(output.status.code(), Some(PROVED), "{}", stdout(&output));
    let out = stdout(&output);
    let json_start = out.find('{').expect("the certificate JSON starts");
    let certificate: serde_json::Value =
        serde_json::from_str(&out[json_start..]).expect("the certificate is JSON");
    let conflict = &certificate["conflicts"][0];
    assert_eq!(conflict["resolution"]["kind"], "defeated", "{certificate}");
    assert_eq!(
        conflict["resolution"]["basis"]["kind"], "priority",
        "{certificate}"
    );
    let edge = &conflict["resolution"]["basis"]["edges"][0];
    assert_eq!(edge["winner"], "example.revision.旧版规则", "{certificate}");
    assert_eq!(edge["loser"], "example.revision.新版规则", "{certificate}");
    let origin = &edge["origin"];
    assert_eq!(origin["kind"], "priority_declaration", "{certificate}");
    assert_eq!(origin["declared_in"], "example.revision", "{certificate}");
    assert_eq!(
        origin["sources"][0]["locator"], "第二十条第三项（从旧兼从轻）",
        "{certificate}"
    );

    // Verify the exported certificate in a second process.
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "std-deduce-cli-{}-historical-cert-{n}.json",
        std::process::id()
    ));
    fs::write(&path, &out[json_start..]).expect("write the certificate");
    let verify = run(vec![
        format!(":load {}", example("历史版本-从旧兼从轻.std")),
        format!(":verify-cert {} {goal}", path.display()),
    ]);
    let _ = fs::remove_file(&path);
    check(
        &verify,
        PROVED,
        &[
            "逻辑校验：通过",
            "内核证明：通过",
            "侧条件：unless 未发现已成立的阻断条件；未决冲突 0 项；根冲突已按记录裁决；优先关系已核验（1 条边）",
        ],
    );
}

/// The loader refuses the group declarations that cannot mean anything: a lone
/// version, a reused rule name inside one group, a version without an effective
/// range, and an identifier that names an existing declaration. Every error
/// carries the rule name and the source position of the clause.
#[test]
fn the_loader_refuses_invalid_revision_groups() {
    // A group needs at least two rules.
    let src = two_versions("旧版规则", "新版规则", "1999-01-01", "2021-01-01");
    let (first, _) = src
        .split_once("rule 新版规则 :")
        .expect("the fixture has two rules");
    let lone = TempTheory::new("lone", first);
    let output = run(vec![lone.path.display().to_string()]);
    check_stderr(
        &output,
        GAP_OR_CONFLICT,
        &[
            "error: `rule 旧版规则` 的 `revision 第二十条`：同一 revision 组内必须至少有两条规则",
            "单条声明不是一组历史版本",
        ],
    );
    let err = stderr(&output);
    assert!(err.contains(":15:3: error:"), "{err}");

    // Two versions of one group may not reuse a rule name.
    let same_name = TempTheory::new(
        "same-name",
        &two_versions("旧版规则", "旧版规则", "1999-01-01", "2021-01-01"),
    );
    let output = run(vec![same_name.path.display().to_string()]);
    check_stderr(
        &output,
        GAP_OR_CONFLICT,
        &[
            "error: `rule 旧版规则` 的 `revision 第二十条`：同一 revision 组内不能有同名规则",
            ":22:3: error:",
        ],
    );

    // Every version must declare an effective range.
    let no_range = TempTheory::new(
        "no-range",
        &two_versions("旧版规则", "新版规则", "1999-01-01", ""),
    );
    let output = run(vec![no_range.path.display().to_string()]);
    check_stderr(
        &output,
        GAP_OR_CONFLICT,
        &[
            "`rule 新版规则` 的 `revision 第二十条`：历史版本必须声明生效区间",
            "请写 `effective <YYYY-MM-DD>`",
        ],
    );

    // The group identifier shares the declaration name space.
    let clash = TempTheory::new(
        "clash",
        &two_versions("旧版规则", "新版规则", "1999-01-01", "2021-01-01")
            .replace("revision 第二十条", "revision 行为"),
    );
    let output = run(vec![clash.path.display().to_string()]);
    check_stderr(
        &output,
        GAP_OR_CONFLICT,
        &[
            "组标识不得与已声明规则名/谓词冲突",
            "`行为` 已声明为 `pred`",
        ],
    );
}
