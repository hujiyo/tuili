//! End-to-end tests for the five trust labels printed by `:why`, `:explain`
//! and `:labels`.
//!
//! Every case is a self-contained theory in its own temporary directory, so the
//! tests do not depend on the repository's lawpacks. The label itself is derived
//! from the certificate's fields by the certificate crate; these tests pin what
//! the user sees and that the three commands agree.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP_OR_CONFLICT: i32 = 1;

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-labels-{}-{tag}-{n}",
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

fn check(output: &Output, expected: i32, needles: &[&str]) {
    assert_exit(output, expected);
    let out = stdout(output);
    let err = stderr(output);
    for needle in needles {
        assert!(
            out.contains(needle),
            "stdout does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
}

/// The `信任：…` lines of an output.
fn trust_lines(out: &str) -> Vec<String> {
    out.lines()
        .filter(|line| line.starts_with("信任："))
        .map(str::to_owned)
        .collect()
}

const VERIFIED: &str = r#"sort 人
pred 违法 : 人 → Prop
pred 受罚 : 人 → Prop
obj 张三 : 人
axiom 张三违法 : 违法 张三
  identity verified
  source text "判决" locator "第一页"
rule 处罚 :
  params p : 人
  premise 违法 p
  conclude 受罚 p
  source text "测试" locator "二"
"#;

const CLAIM: &str = r#"sort 人
pred 违法 : 人 → Prop
pred 受罚 : 人 → Prop
obj 张三 : 人
axiom 张三违法 : 违法 张三
  source text "案情" locator "一"
rule 处罚 :
  params p : 人
  premise 违法 p
  conclude 受罚 p
  source text "测试" locator "二"
"#;

/// One strict fact and one claim, both premises of the root rule.
const MIXED: &str = r#"sort 人
pred 违法 : 人 → Prop
pred 情节 : 人 → Prop
pred 受罚 : 人 → Prop
obj 张三 : 人
axiom 张三违法 : 违法 张三
  identity verified
  source text "判决" locator "第一页"
axiom 张三情节 : 情节 张三
  source text "案情" locator "二"
rule 处罚 :
  params p : 人
  premise 违法 p
  premise 情节 p
  conclude 受罚 p
  source text "测试" locator "三"
"#;

const GAP: &str = r#"sort 人
pred 违法 : 人 → Prop
pred 受罚 : 人 → Prop
obj 张三 : 人
rule 处罚 :
  params p : 人
  premise 违法 p
  conclude 受罚 p
  source text "测试" locator "二"
"#;

const CONFLICT: &str = r#"sort 申请
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
contrary 批准 不批准
obj 甲 : 申请
rule 批准规则 :
  conclude 批准 甲
  source text "测试" locator "一"
rule 不批准规则 :
  conclude 不批准 甲
  source text "测试" locator "二"
"#;

const OPEN_CONCEPT: &str = r#"sort 人
pred 损害 : 人 → Prop
pred 重大 : 人 → Prop
obj 甲 : 人
open 重大
axiom 损害事实 : 损害 甲
  source text "案件" locator "一"
rule 重大推定 :
  params x : 人
  premise 损害 x
  conclude 重大 x
  source text "测试" locator "二"
"#;

const LOCAL_EXTENSION: &str = r#"sort 人
pred 有过错 : 人 → Prop
pred 应赔偿 : 人 → Prop
obj 甲 : 人
axiom 甲有过错 : 有过错 甲
  source text "案情" locator "一"
rule 赔偿规则 :
  params x : 人
  premise 有过错 x
  conclude 应赔偿 x
  source text "案件规则" locator "二"
"#;

/// A proved root that uses a claim, while an unrelated conflict elsewhere is
/// unresolved. The conflict is not root-relevant, so the root is only
/// `依赖假设`; the unrelated conflict must not become `争点未决`.
const CLAIM_WITH_UNRELATED_CONFLICT: &str = r#"sort 人
pred 违法 : 人 → Prop
pred 受罚 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
contrary 批准 不批准
obj 张三 : 人
obj 甲 : 人
axiom 张三违法 : 违法 张三
  source text "案情" locator "一"
rule 处罚 :
  params p : 人
  premise 违法 p
  conclude 受罚 p
  source text "测试" locator "二"
rule 批准规则 :
  conclude 批准 甲
  source text "测试" locator "三"
rule 不批准规则 :
  conclude 不批准 甲
  source text "测试" locator "四"
"#;

/// The same unrelated unresolved conflict on a strict-fact proof: the root
/// keeps `已验证` and the unrelated branch does not make it `争点未决`.
const VERIFIED_WITH_UNRELATED_CONFLICT: &str = r#"sort 人
pred 违法 : 人 → Prop
pred 受罚 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
contrary 批准 不批准
obj 张三 : 人
obj 甲 : 人
axiom 张三违法 : 违法 张三
  identity verified
  source text "判决" locator "第一页"
rule 处罚 :
  params p : 人
  premise 违法 p
  conclude 受罚 p
  source text "测试" locator "二"
rule 批准规则 :
  conclude 批准 甲
  source text "测试" locator "三"
rule 不批准规则 :
  conclude 不批准 甲
  source text "测试" locator "四"
"#;

const TWO_JURISDICTIONS: &str = r#"sort 人
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
"#;

/// The root is proved by the official pack rule. The case also declares a
/// local rule that only derives an unrelated conclusion, so its
/// `local-extension` obligation is not on the root's proof graph.
const UNRELATED_LOCAL_EXTENSION: &str = r#"import cn.constitution

pred 本地无关 : cn.constitution.人 → Prop

obj 张三 : cn.constitution.人
obj 甲宅 : cn.constitution.住宅

axiom 张三住宅遭非法搜查 : cn.constitution.非法搜查 张三 甲宅
  source text "示例案情" locator "某次搜查"
axiom 张三是公民 : cn.constitution.公民 张三
  source text "示例案情" locator "当事人身份"

rule 本地无关规则 :
  params p : cn.constitution.人, h : cn.constitution.住宅
  premise cn.constitution.非法搜查 p h
  conclude 本地无关 p
  source text "案件规则" locator "一"
"#;

/// The goal is in an unresolved conflict, while the fixed point also contains
/// a rule whose `unless` blocker the checker's conservative closure derives
/// without a proof. The conflict branch must run the layers before it prints a
/// label.
const CONFLICT_WITH_UNCLEARED_BLOCKER: &str = r#"sort 人
obj 张三 : 人
obj 李四 : 人
obj 甲 : 人
pred 侵占 : 人 → Prop
pred 违法 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
pred 无辜 : 人 → Prop
pred 佐证 : 侵占 李四 → Prop
contrary 批准 不批准
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"
rule 依赖推定 :
  premise h : 侵占 李四
  unless 佐证 h
  conclude 无辜 张三
  source text "测试" locator "夹具"
rule r :
  params p : 人
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
rule 批准规则 :
  conclude 批准 甲
  source text "测试" locator "夹具"
rule 不批准规则 :
  conclude 不批准 甲
  source text "测试" locator "夹具"
"#;

#[test]
fn five_minimal_cases_trigger_five_labels() {
    let dir = TempDir::new("five");

    let verified = dir.write("verified.std", VERIFIED);
    check(
        &session(&verified, &[], &[":labels 受罚 张三"]),
        PROVED,
        &["信任：已验证", "模型内", "这不等同于法律上正确"],
    );

    let claim = dir.write("claim.std", CLAIM);
    check(
        &session(&claim, &[], &[":labels 受罚 张三"]),
        PROVED,
        &["信任：依赖假设", "据用户陈述 1 条"],
    );

    let mixed = dir.write("mixed.std", MIXED);
    check(
        &session(&mixed, &[], &[":labels 受罚 张三"]),
        PROVED,
        &[
            "信任：依赖假设",
            "据用户陈述 1 条",
            "同时使用严格事实（法院查明 1 条、双方无争议 0 条）",
        ],
    );

    let gap = dir.write("gap.std", GAP);
    check(
        &session(&gap, &[], &[":labels 受罚 张三"]),
        GAP_OR_CONFLICT,
        &["信任：事实待举证", "根为缺口", "缺少前提义务 1 项"],
    );

    let conflict = dir.write("conflict.std", CONFLICT);
    check(
        &session(&conflict, &[], &[":labels 批准 甲"]),
        GAP_OR_CONFLICT,
        &["信任：争点未决", "未决冲突 1 项", "另含：事实待举证"],
    );

    let open = dir.write("open.std", OPEN_CONCEPT);
    check(
        &session(&open, &[], &[":labels 重大 甲"]),
        GAP_OR_CONFLICT,
        &["信任：需律师判断", "开放概念义务 1 项"],
    );

    let local = dir.write("local.std", LOCAL_EXTENSION);
    check(
        &session(
            &local,
            &["--closed-env", "--allow-case-rules"],
            &[":labels 应赔偿 甲"],
        ),
        GAP_OR_CONFLICT,
        &["信任：需律师判断", "案件扩展义务 1 项", "`local-extension`"],
    );
}

#[test]
fn an_unrelated_conflict_does_not_change_the_root_label() {
    let dir = TempDir::new("claim-conflict");
    let claim = dir.write("claim-conflict.std", CLAIM_WITH_UNRELATED_CONFLICT);
    let output = session(&claim, &[], &[":labels 受罚 张三"]);
    check(&output, PROVED, &["信任：依赖假设", "据用户陈述 1 条"]);
    let out = stdout(&output);
    assert!(!out.contains("争点未决"), "{out}");
    assert!(
        !out.contains("需律师判断"),
        "an unrelated conflict must not affect the root's label:\n{out}"
    );

    let verified = dir.write("verified-conflict.std", VERIFIED_WITH_UNRELATED_CONFLICT);
    let output = session(&verified, &[], &[":labels 受罚 张三"]);
    check(&output, PROVED, &["信任：已验证", "根可达子图无未决义务"]);
    let out = stdout(&output);
    assert!(!out.contains("争点未决"), "{out}");
    assert!(!out.contains("需律师判断"), "{out}");
}

#[test]
fn why_explain_and_labels_print_the_same_trust_line() {
    let dir = TempDir::new("agree");
    let open = dir.write("open.std", OPEN_CONCEPT);
    let output = session(
        &open,
        &[],
        &[":why 重大 甲", ":explain 重大 甲", ":labels 重大 甲"],
    );
    let out = stdout(&output);
    let lines = trust_lines(&out);
    assert_eq!(lines.len(), 3, "one trust line per command:\n{out}");
    assert!(
        lines.iter().all(|line| line == &lines[0]),
        "the three commands must print the same trust line:\n{out}"
    );
    assert!(lines[0].starts_with("信任：需律师判断"), "{}", lines[0]);

    // The same target in a gap case must agree too.
    let gap = dir.write("gap.std", GAP);
    let output = session(
        &gap,
        &[],
        &[":why 受罚 张三", ":explain 受罚 张三", ":labels 受罚 张三"],
    );
    let lines = trust_lines(&stdout(&output));
    assert_eq!(lines.len(), 3, "{}", stdout(&output));
    assert!(lines.iter().all(|line| line == &lines[0]));
    assert!(lines[0].starts_with("信任：事实待举证"), "{}", lines[0]);

    // A mixed strict/claim proof must print the same counts everywhere.
    let mixed = dir.write("mixed.std", MIXED);
    let output = session(
        &mixed,
        &[],
        &[":why 受罚 张三", ":explain 受罚 张三", ":labels 受罚 张三"],
    );
    let lines = trust_lines(&stdout(&output));
    assert_eq!(lines.len(), 3, "{}", stdout(&output));
    assert!(lines.iter().all(|line| line == &lines[0]));
    assert!(lines[0].starts_with("信任：依赖假设"), "{}", lines[0]);
    assert!(lines[0].contains("据用户陈述 1 条"), "{}", lines[0]);
    assert!(
        lines[0].contains("同时使用严格事实（法院查明 1 条、双方无争议 0 条）"),
        "{}",
        lines[0]
    );
}

#[test]
fn an_unresolved_conflict_is_never_reported_as_verified_or_a_mere_assumption() {
    let dir = TempDir::new("conflict-boundary");
    let conflict = dir.write("conflict.std", CONFLICT);
    let output = session(&conflict, &[], &[":why 批准 甲", ":labels 批准 甲"]);
    let out = stdout(&output);
    let lines = trust_lines(&out);
    assert_eq!(lines.len(), 2, "{out}");
    assert!(lines.iter().all(|line| line == &lines[0]), "{out}");
    assert!(lines[0].contains("争点未决"), "{out}");
    assert!(!out.contains("已验证"), "{out}");
    assert!(!out.contains("需律师判断"), "{out}");
    assert!(!lines[0].contains("依赖假设（"), "{out}");
}

#[test]
fn a_gap_root_is_never_reported_as_verified() {
    let dir = TempDir::new("gap-boundary");
    let gap = dir.write("gap.std", GAP);
    let output = session(&gap, &[], &[":why 受罚 张三", ":labels 受罚 张三"]);
    let out = stdout(&output);
    let lines = trust_lines(&out);
    assert_eq!(lines.len(), 2, "{out}");
    assert!(lines.iter().all(|line| line == &lines[0]), "{out}");
    assert!(lines[0].starts_with("信任：事实待举证"), "{out}");
    assert!(!out.contains("已验证"), "{out}");
    assert!(
        !out.contains("另含：已验证"),
        "the label list must not smuggle 已验证 as a secondary label:\n{out}"
    );
}

#[test]
fn cert_json_keeps_the_v10_top_level_fields_and_no_label_field() {
    let dir = TempDir::new("cert-shape");
    let verified = dir.write("verified.std", VERIFIED);
    let output = session(&verified, &[], &[":cert 受罚 张三"]);
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    let json: serde_json::Value =
        serde_json::from_str(text[start..].trim_end()).expect("the certificate JSON parses");
    let object = json.as_object().expect("the certificate JSON is an object");
    let mut keys: Vec<&str> = object.keys().map(String::as_str).collect();
    keys.sort_unstable();
    assert_eq!(
        keys,
        [
            "alternatives",
            "assumptions",
            "conflicts",
            "environment",
            "format_version",
            "interpretations",
            "metadata",
            "nodes",
            "open_obligations",
            "root",
        ],
        "the certificate must keep exactly v10's top-level fields: {text}"
    );
    assert_eq!(object["format_version"], 10, "{text}");
    for unexpected in ["trust", "labels", "label", "trust_labels"] {
        assert!(
            !object.contains_key(unexpected),
            "a label must not be written into the certificate: {unexpected}\n{text}"
        );
    }
}

#[test]
fn labels_are_byte_identical_for_the_same_case() {
    let dir = TempDir::new("deterministic");
    let mixed = dir.write("mixed.std", MIXED);
    let first = session(&mixed, &[], &[":labels 受罚 张三", ":why 受罚 张三"]);
    let second = session(&mixed, &[], &[":labels 受罚 张三", ":why 受罚 张三"]);
    assert_eq!(stdout(&first), stdout(&second));
    assert_eq!(stderr(&first), stderr(&second));
}

#[test]
fn two_labels_commands_in_one_session_are_byte_identical() {
    let dir = TempDir::new("same-session");
    let mixed = dir.write("mixed.std", MIXED);
    let output = session(&mixed, &[], &[":labels 受罚 张三", ":labels 受罚 张三"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let lines = trust_lines(&out);
    assert_eq!(lines.len(), 2, "{out}");
    let first = out.find("信任：").expect("the first summary is there");
    let marker = "信任：".len();
    let second = out[first + marker..]
        .find("信任：")
        .map(|offset| first + marker + offset)
        .expect("the second summary is there");
    assert_eq!(
        &out[first..second],
        &out[second..],
        "two :labels runs in one session must be byte-identical:\n{out}"
    );
}

#[test]
fn labels_error_paths_are_named() {
    // No target.
    let dir = TempDir::new("errors");
    let claim = dir.write("claim.std", CLAIM);
    let output = session(&claim, &[], &[":labels"]);
    assert_exit(&output, 2);
    assert!(
        stderr(&output).contains("用法：:labels <目标命题>"),
        "{}",
        stderr(&output)
    );

    // No theory loaded.
    let output = run(&[
        "--no-default-packs".to_owned(),
        ":labels 受罚 张三".to_owned(),
    ]);
    assert_exit(&output, 2);
    assert!(
        stderr(&output).contains("尚未加载理论"),
        "{}",
        stderr(&output)
    );

    // Two jurisdictions without a session choice.
    let two = dir.write("two-jurisdictions.std", TWO_JURISDICTIONS);
    let output = session(&two, &[], &[":labels Q 甲"]);
    assert_exit(&output, 2);
    assert!(
        stderr(&output).contains("必须用 --jurisdiction 或 :jurisdiction 选择管辖"),
        "{}",
        stderr(&output)
    );
    assert!(
        !stdout(&output).contains("信任："),
        "an error path must not print a label:\n{}",
        stdout(&output)
    );
}

#[test]
fn cert_and_labels_exit_codes_keep_their_own_semantics() {
    let dir = TempDir::new("exit-codes");
    let open = dir.write("open.std", OPEN_CONCEPT);
    let cert = session(&open, &[], &[":cert 重大 甲"]);
    assert_exit(&cert, PROVED);
    let labels = session(&open, &[], &[":labels 重大 甲"]);
    assert_exit(&labels, GAP_OR_CONFLICT);
    assert!(
        stdout(&labels).contains("信任：需律师判断"),
        "{}",
        stdout(&labels)
    );

    // `:cert` still follows root reachability: a gap root exits 1, not 0.
    let gap = dir.write("gap.std", GAP);
    let cert = session(&gap, &[], &[":cert 受罚 张三"]);
    assert_exit(&cert, GAP_OR_CONFLICT);
    let labels = session(&gap, &[], &[":labels 受罚 张三"]);
    assert_exit(&labels, GAP_OR_CONFLICT);
}

#[test]
fn an_unrelated_local_extension_is_not_needed_by_the_root() {
    // The root is proved by the official pack rule; the case file also declares
    // a local rule that only derives an unrelated conclusion. The
    // `local-extension` obligation names that unrelated node, so the label
    // layer must not turn the root into 需律师判断.
    let dir = TempDir::new("local-unrelated");
    let case = dir.write("case.std", UNRELATED_LOCAL_EXTENSION);
    let output = session(
        &case,
        &["--closed-env", "--allow-case-rules"],
        &[":labels cn.constitution.住宅受侵犯 张三 甲宅"],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("信任：依赖假设"), "{out}");
    assert!(!out.contains("需律师判断"), "{out}");
    assert!(!out.contains("案件扩展义务"), "{out}");
}

#[test]
fn a_conflict_branch_checks_before_printing_the_trust_line() {
    let dir = TempDir::new("conflict-check");
    let case = dir.write("unclear-blocker.std", CONFLICT_WITH_UNCLEARED_BLOCKER);
    for command in [":why 批准 甲", ":labels 批准 甲"] {
        let output = session(&case, &[], &[command]);
        assert_exit(&output, 2);
        let out = stdout(&output);
        let err = stderr(&output);
        assert!(out.contains("逻辑校验失败"), "{command}\n{out}\n{err}");
        assert!(
            !out.contains("信任："),
            "a certificate that fails its layers must not print a trust line ({command}):\n{out}\n{err}"
        );
    }
}

#[test]
fn the_label_line_is_not_part_of_the_derivation_tree() {
    let dir = TempDir::new("tree");
    let claim = dir.write("claim.std", CLAIM);
    let output = session(&claim, &[], &[":why 受罚 张三"]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let lines: Vec<&str> = out.lines().collect();
    let result = lines
        .iter()
        .position(|line| *line == "推导已通过独立校验。")
        .unwrap_or_else(|| panic!("no result line:\n{out}"));
    assert_eq!(lines[result + 1], "信任：依赖假设（据用户陈述 1 条）");
    for line in lines {
        assert!(
            !(line.contains("信任：") && line.contains('▸')),
            "the label must not be spliced into the tree: {line:?}\n{out}"
        );
    }
}
