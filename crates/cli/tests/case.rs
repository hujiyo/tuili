//! End-to-end tests for the strict, versioned JSON case description.
//!
//! Every case runs through the real binary. The fixture is
//! `examples/案件-住宅搜查.json`; malformed variants are derived from it so a
//! rejection test isolates the one field it changes. Assertions pin the exit
//! code, the JSON path in the diagnostic and one short message, not a whole
//! output snapshot.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use serde_json::{json, Value};

const PROVED: i32 = 0;
/// The batch entry reports a rejected JSON case description as a command-style
/// error, the same code `:load-case` uses.
const LOAD_ERROR: i32 = 2;
/// A query after a successful load can still fail because its target is a gap;
/// that is a proof outcome, not a JSON load rejection.
const QUERY_FAILED: i32 = 1;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root exists")
}

fn example(name: &str) -> String {
    let path = repo_root().join("examples").join(name);
    assert!(path.is_file(), "missing example file: {}", path.display());
    path.to_string_lossy().into_owned()
}

fn run_in(current_dir: &Path, args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run(args: &[String]) -> Output {
    run_in(&repo_root(), args)
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

/// A temporary directory outside the repository, removed when the test ends.
struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("std-deduce-case-{}-{tag}-{n}", std::process::id()));
        fs::create_dir_all(&path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn write(&self, name: &str, contents: &str) -> PathBuf {
        let path = self.path.join(name);
        fs::write(&path, contents).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        path
    }

    fn write_bytes(&self, name: &str, contents: &[u8]) -> PathBuf {
        let path = self.path.join(name);
        fs::write(&path, contents).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn example_case() -> Value {
    let text = fs::read_to_string(example("案件-住宅搜查.json"))
        .expect("the canonical case description is readable");
    serde_json::from_str(&text).expect("the canonical case description is valid JSON")
}

fn run_value(value: &Value) -> Output {
    run_value_with(value, &[])
}

fn run_value_with(value: &Value, options: &[&str]) -> Output {
    let temp = TempDir::new("value");
    let path = temp.write("case.json", &value.to_string());
    let mut args: Vec<String> = options.iter().map(|option| (*option).to_owned()).collect();
    args.push(path.to_string_lossy().into_owned());
    run(&args)
}

/// Load a `.std` theory from a file, then load the JSON case from a file in the
/// same session. This exercises the real load path for both files: the theory
/// supplies the ledger names a JSON object must not reuse, and the JSON case is
/// rejected by `:load-case`, not by a directly constructed structure.
fn run_theory_then_case(theory: &str, case: &Value, options: &[&str]) -> Output {
    let temp = TempDir::new("theory-then-case");
    let theory_path = temp.write("theory.std", theory);
    let case_path = temp.write("case.json", &case.to_string());
    let mut args: Vec<String> = options.iter().map(|option| (*option).to_owned()).collect();
    args.push(theory_path.to_string_lossy().into_owned());
    args.push(format!(":load-case {}", case_path.display()));
    // The temporary directory has no `lawpacks`, so the auto environment stays
    // disabled and the test exercises only the two files it wrote.
    run_in(temp.path(), &args)
}

fn assert_load_error(output: &Output, json_path: &str, message: &str) {
    assert_exit(output, LOAD_ERROR);
    let err = stderr(output);
    assert!(
        err.contains(json_path),
        "stderr does not name the JSON path {json_path:?}:\n{err}"
    );
    assert!(
        err.contains(message),
        "stderr does not contain {message:?}:\n{err}"
    );
}

// -------------------------------------------------------------------------
// Success paths
// -------------------------------------------------------------------------

#[test]
fn a_valid_case_loads_three_identities_and_proves_its_goal() {
    let case = example("案件-住宅搜查.json");
    let output = run(&[case, ":why cn.constitution.住宅受侵犯 张三 甲宅".to_owned()]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    for needle in [
        "已加载案件",
        "（住宅搜查）",
        "+ 张三",
        "+ 甲宅",
        "+ 事实1",
        "事实身份：法院查明 1、用户陈述 1、对方争议 1",
        "· 目标 cn.constitution.住宅受侵犯 张三 甲宅",
        "推导已通过独立校验。",
    ] {
        assert!(out.contains(needle), "missing {needle:?}:\n{out}");
    }
}

#[test]
fn the_batch_json_entry_and_load_case_command_agree() {
    let case = example("案件-住宅搜查.json");
    let batch = run(std::slice::from_ref(&case));
    let command = run(&[format!(":load-case {case}")]);
    assert_exit(&batch, PROVED);
    assert_exit(&command, PROVED);
    assert_eq!(
        stdout(&batch),
        stdout(&command),
        "the two entry points must report the same load"
    );
}

#[test]
fn reference_values_become_explicit_session_values() {
    let case = example("案件-住宅搜查.json");
    let output = run(&[case, ":asof".to_owned(), ":jurisdiction".to_owned()]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("基准日：2020-05-06（案件）"), "{out}");
    assert!(out.contains("管辖：CN（案件）"), "{out}");
}

#[test]
fn reference_equal_to_the_command_line_loads() {
    let case = example("案件-住宅搜查.json");
    let output = run(&[
        "--as-of".to_owned(),
        "2020-05-06".to_owned(),
        "--jurisdiction".to_owned(),
        "CN".to_owned(),
        case,
        ":why cn.constitution.住宅受侵犯 张三 甲宅".to_owned(),
    ]);
    assert_exit(&output, PROVED);
}

#[test]
fn a_disputed_fact_is_registered_but_never_a_premise() {
    let case = example("案件-住宅搜查.json");
    let output = run(&[
        case,
        ":fact list".to_owned(),
        ":why cn.constitution.非法侵入 张三 甲宅".to_owned(),
    ]);
    // The query is a gap, so the session exits non-zero even though the load
    // succeeded.
    assert_exit(&output, QUERY_FAILED);
    let out = stdout(&output);
    assert!(out.contains("对方争议"), "{out}");
    assert!(out.contains("争议事实，不参与推导"), "{out}");
    assert!(out.contains("根为缺口"), "{out}");
}

#[test]
fn an_assumption_is_registered_with_the_assumed_identity() {
    let value = json!({
        "schema_version": 1,
        "imports": ["cn.constitution"],
        "objects": [
            {"name": "张三", "type": "cn.constitution.人"},
            {"name": "甲宅", "type": "cn.constitution.住宅"}
        ],
        "facts": [],
        "assumptions": [
            {
                "proposition": "cn.constitution.非法搜查 张三 甲宅",
                "identity": "assumed",
                "source": {"text": "分析假设", "locator": "假设一"}
            }
        ],
        "goals": ["cn.constitution.住宅受侵犯 张三 甲宅"]
    });
    let output = run_value(&value);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("事实身份：分析假设 1"), "{out}");
    assert!(out.contains("+ 事实1"), "{out}");
}

#[test]
fn a_case_without_imports_loads_under_no_default_packs() {
    let value = json!({
        "schema_version": 1,
        "imports": [],
        "facts": [],
        "goals": ["∀ (p : Prop), p → p"]
    });
    let temp = TempDir::new("no-registry");
    let path = temp.write("case.json", &value.to_string());
    let output = run_in(
        temp.path(),
        &[
            "--no-default-packs".to_owned(),
            path.to_string_lossy().into_owned(),
        ],
    );
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains("· 目标 ∀ (p : Prop)"), "{out}");
}

#[test]
fn goals_are_listed_but_not_proved_by_the_load() {
    // The goal is well-typed but has no fact backing it. Loading lists it and
    // succeeds: `goals` is a target list for later `:why` / `:cert` /
    // `:review`, not an automatic proof obligation.
    let mut value = example_case();
    value["facts"] = json!([]);
    value["assumptions"] = json!([]);
    let output = run_value(&value);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("· 目标 cn.constitution.住宅受侵犯 张三 甲宅"),
        "{out}"
    );
    assert!(!out.contains("推导已通过独立校验。"), "{out}");
    assert!(!out.contains("根为缺口"), "{out}");
}

#[test]
fn batch_json_exit_codes_are_2_for_rejection_and_0_for_success() {
    let success = run(&[example("案件-住宅搜查.json")]);
    assert_exit(&success, PROVED);

    let temp = TempDir::new("exit-codes");
    let malformed = temp.write("bad.json", "{\"schema_version\":1,");
    let bad_json = run(&[malformed.to_string_lossy().into_owned()]);
    assert_exit(&bad_json, LOAD_ERROR);
    assert!(
        stderr(&bad_json).contains("JSON 解析失败"),
        "{}",
        stderr(&bad_json)
    );

    let mut value = example_case();
    value["schema_version"] = json!(9);
    let bad_field = run_value(&value);
    assert_exit(&bad_field, LOAD_ERROR);
    assert!(
        stderr(&bad_field).contains("schema_version"),
        "{}",
        stderr(&bad_field)
    );
}

#[test]
fn the_closed_environment_loads_a_json_case() {
    let case = example("案件-住宅搜查.json");
    let output = run(&[
        "--closed-env".to_owned(),
        case,
        ":why cn.constitution.住宅受侵犯 张三 甲宅".to_owned(),
    ]);
    assert_exit(&output, PROVED);
    assert!(
        stdout(&output).contains("推导已通过独立校验。"),
        "{}",
        stdout(&output)
    );
}

// -------------------------------------------------------------------------
// Reference conflicts
// -------------------------------------------------------------------------

#[test]
fn a_reference_date_conflict_with_the_command_line_is_an_error() {
    let case = example("案件-住宅搜查.json");
    let output = run(&["--as-of".to_owned(), "2021-01-01".to_owned(), case]);
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(err.contains("reference.as_of"), "{err}");
    assert!(err.contains("冲突"), "{err}");
}

#[test]
fn a_reference_jurisdiction_conflict_with_the_command_line_is_an_error() {
    let case = example("案件-住宅搜查.json");
    let output = run(&["--jurisdiction".to_owned(), "US".to_owned(), case]);
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(err.contains("reference.jurisdiction"), "{err}");
    assert!(err.contains("冲突"), "{err}");
}

// -------------------------------------------------------------------------
// Schema rejections
// -------------------------------------------------------------------------

#[test]
fn an_unknown_schema_version_is_rejected() {
    let mut value = example_case();
    value["schema_version"] = json!(2);
    assert_load_error(&run_value(&value), "schema_version", "不支持的");
}

#[test]
fn a_missing_schema_version_is_rejected() {
    let mut value = example_case();
    value.as_object_mut().unwrap().remove("schema_version");
    assert_load_error(&run_value(&value), "schema_version", "缺少必填字段");
}

#[test]
fn an_unknown_top_level_field_is_rejected() {
    let mut value = example_case();
    value
        .as_object_mut()
        .unwrap()
        .insert("colour".to_owned(), json!("red"));
    assert_load_error(&run_value(&value), "colour", "未知字段");
}

#[test]
fn a_rule_field_is_rejected_as_defining_law() {
    let mut value = example_case();
    value
        .as_object_mut()
        .unwrap()
        .insert("rule".to_owned(), json!({"name": "新规则"}));
    assert_load_error(&run_value(&value), "rule", "不能定义法律");
}

#[test]
fn a_pred_field_inside_a_fact_is_rejected_as_defining_law() {
    let mut value = example_case();
    value["facts"][0]
        .as_object_mut()
        .unwrap()
        .insert("pred".to_owned(), json!("新谓词"));
    assert_load_error(&run_value(&value), "facts[0].pred", "不能定义法律");
}

#[test]
fn a_missing_identity_is_rejected() {
    let mut value = example_case();
    value["facts"][0]
        .as_object_mut()
        .unwrap()
        .remove("identity");
    assert_load_error(&run_value(&value), "facts[0].identity", "缺少必填字段");
}

#[test]
fn an_unknown_identity_is_rejected() {
    let mut value = example_case();
    value["facts"][0]["identity"] = json!("court");
    assert_load_error(&run_value(&value), "facts[0].identity", "不是合法身份");
}

#[test]
fn an_empty_source_text_is_rejected() {
    let mut value = example_case();
    value["facts"][0]["source"]["text"] = json!("   ");
    assert_load_error(&run_value(&value), "facts[0].source.text", "不能为空");
}

#[test]
fn a_bad_occurred_at_is_rejected() {
    let mut value = example_case();
    value["facts"][0]["occurred_at"] = json!("2020-02-30");
    assert_load_error(&run_value(&value), "facts[0].occurred_at", "超出");
}

#[test]
fn a_bad_occurred_in_is_rejected() {
    let mut value = example_case();
    value["facts"][0]["occurred_in"] = json!("CN HN");
    assert_load_error(&run_value(&value), "facts[0].occurred_in", "非法字符");
}

#[test]
fn a_proposition_that_does_not_type_check_is_rejected_with_its_path() {
    let mut value = example_case();
    value["facts"][0]["proposition"] = json!("cn.constitution.非法搜查 张三");
    let output = run_value(&value);
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(err.contains("facts[0].proposition"), "{err}");
    assert!(err.contains("命题"), "{err}");
}

#[test]
fn goals_that_are_not_propositions_are_rejected() {
    // A sort's type (`Type`) and a function type are not propositions. Both
    // must fail at the goal's own JSON path.
    for goal in [
        "cn.constitution.人",
        "cn.constitution.人 → cn.constitution.人",
    ] {
        let mut value = example_case();
        value["goals"][0] = json!(goal);
        assert_load_error(&run_value(&value), "goals[0].proposition", "类型检查失败");
    }
}

#[test]
fn an_assumption_with_a_non_assumed_identity_is_rejected() {
    let value = json!({
        "schema_version": 1,
        "imports": [],
        "facts": [],
        "assumptions": [
            {
                "proposition": "p",
                "identity": "user_asserted",
                "source": {"text": "a", "locator": "b"}
            }
        ]
    });
    assert_load_error(
        &run_value(&value),
        "assumptions[0].identity",
        "用户陈述请写在 facts 里",
    );
}

#[test]
fn an_assumption_cannot_claim_a_court_finding() {
    let value = json!({
        "schema_version": 1,
        "imports": [],
        "facts": [],
        "assumptions": [
            {
                "proposition": "p",
                "identity": "verified",
                "source": {"text": "判决书", "locator": "查明事实"}
            }
        ]
    });
    assert_load_error(
        &run_value(&value),
        "assumptions[0].identity",
        "分析假设不能声称法院查明",
    );
}

#[test]
fn an_object_that_names_a_concept_instead_of_a_sort_is_rejected() {
    let value = json!({
        "schema_version": 1,
        "imports": [],
        "facts": [],
        "objects": [{"name": "恶意", "type": "Prop"}]
    });
    let output = run_value_with(&value, &["--no-default-packs"]);
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(err.contains("objects[0].type"), "{err}");
    assert!(err.contains("sort"), "{err}");
}

#[test]
fn an_object_type_that_is_not_declared_is_rejected() {
    let value = json!({
        "schema_version": 1,
        "imports": [],
        "facts": [],
        "objects": [{"name": "甲", "type": "未声明类型"}]
    });
    let output = run_value_with(&value, &["--no-default-packs"]);
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(err.contains("objects[0].type"), "{err}");
    assert!(
        err.contains("未知名称") || err.contains("类型检查失败"),
        "{err}"
    );
}

/// One theory declaring every ledger kind, so the collision test can load it
/// from a file and then try to reuse each name as a JSON object.
const DECLARATION_KINDS_THEORY: &str = "\
sort 类型甲\n\
obj 个体甲 : 类型甲\n\
pred 谓词甲 : 类型甲 → Prop\n\
axiom 常量甲 : 类型甲\n\
  source text \"测试\" locator \"夹具\"\n\
axiom 事实甲 : 谓词甲 个体甲\n\
  source text \"测试\" locator \"夹具\"\n\
def 定义甲 : 类型甲 := 个体甲\n\
rule 规则甲 :\n\
  params x : 类型甲\n\
  premise 谓词甲 x\n\
  conclude 谓词甲 x\n\
  source text \"测试\" locator \"夹具\"\n\
interpret 解释甲 : 谓词甲 个体甲 → 谓词甲 个体甲\n\
  direction literal\n\
  source text \"测试\" locator \"夹具\" version \"1\"\n";

#[test]
fn an_object_name_cannot_reuse_any_loaded_declaration() {
    for name in [
        "类型甲",
        "个体甲",
        "谓词甲",
        "常量甲",
        "事实甲",
        "定义甲",
        "规则甲",
        "解释甲",
    ] {
        let value = json!({
            "schema_version": 1,
            "imports": [],
            "facts": [],
            "objects": [{"name": name, "type": "类型甲"}]
        });
        let output =
            run_theory_then_case(DECLARATION_KINDS_THEORY, &value, &["--no-default-packs"]);
        assert_exit(&output, LOAD_ERROR);
        let err = stderr(&output);
        assert!(err.contains("objects[0].name"), "{name}: {err}");
        assert!(err.contains(name), "{name}: {err}");
        assert!(err.contains("名称已被占用"), "{name}: {err}");
    }
}

#[test]
fn duplicate_object_names_are_rejected_even_with_different_types() {
    let mut value = example_case();
    value["objects"] = json!([
        {"name": "张三", "type": "cn.constitution.人"},
        {"name": "张三", "type": "cn.constitution.住宅"}
    ]);
    assert_load_error(&run_value(&value), "objects[1].name", "重复声明");
}

#[test]
fn the_closed_environment_requires_an_object_type_from_a_loaded_pack() {
    // A case-local sort loaded with `--allow-case-rules` is a legal concept the
    // case declared. The JSON format must not let an object use it: in the
    // closed environment the sort has to come from a loaded legal pack.
    let value = json!({
        "schema_version": 1,
        "imports": [],
        "facts": [],
        "objects": [{"name": "甲", "type": "类型甲"}]
    });
    let output = run_theory_then_case(
        "sort 类型甲\n",
        &value,
        &["--closed-env", "--allow-case-rules", "--no-default-packs"],
    );
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(err.contains("objects[0].type"), "{err}");
    assert!(err.contains("包"), "{err}");
}

#[test]
fn duplicate_propositions_with_different_identities_are_rejected() {
    let mut value = example_case();
    let mut duplicate = value["facts"][1].clone();
    duplicate["identity"] = json!("verified");
    value["facts"].as_array_mut().unwrap().push(duplicate);
    assert_load_error(&run_value(&value), "facts[3].identity", "同一命题");
}

// -------------------------------------------------------------------------
// Limits and malformed input
// -------------------------------------------------------------------------

#[test]
fn an_array_over_the_limit_is_rejected() {
    let goals: Vec<Value> = (0..10_001).map(|_| json!("p")).collect();
    let value = json!({
        "schema_version": 1,
        "imports": [],
        "facts": [],
        "goals": goals
    });
    assert_load_error(&run_value(&value), "goals", "上限");
}

#[test]
fn a_deeply_nested_document_is_rejected_without_panicking() {
    let text = format!(
        "{{\"schema_version\":1,\"imports\":[],\"facts\":[],\"goals\":{}{}}}",
        "[".repeat(200),
        "]".repeat(200)
    );
    let temp = TempDir::new("deep");
    let path = temp.write("case.json", &text);
    let output = run(&[path.to_string_lossy().into_owned()]);
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(err.contains("嵌套深度"), "{err}");
}

#[test]
fn malformed_json_is_rejected() {
    let temp = TempDir::new("malformed");
    let path = temp.write("case.json", "{\"schema_version\":1,");
    let output = run(&[path.to_string_lossy().into_owned()]);
    assert_exit(&output, LOAD_ERROR);
    assert!(
        stderr(&output).contains("JSON 解析失败"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn an_oversized_document_is_rejected_before_parsing() {
    const LIMIT: usize = 8 * 1024 * 1024;
    let temp = TempDir::new("oversized");
    let path = temp.write_bytes("case.json", &vec![b' '; LIMIT + 1]);
    let output = run(&[path.to_string_lossy().into_owned()]);
    assert_exit(&output, LOAD_ERROR);
    let err = stderr(&output);
    assert!(err.contains("字节上限"), "{err}");
}

#[test]
fn load_keeps_reading_the_std_grammar_regardless_of_the_extension() {
    // A `.std` theory whose file happens to be named `.json` must still load
    // through `:load`: the command's grammar is chosen by the command, not by
    // the extension. Only the batch entry reserves `.json` for case
    // descriptions.
    let temp = TempDir::new("std-json");
    let path = temp.write(
        "theory.json",
        "sort 人\nobj 张三 : 人\npred 好人 : 人 → Prop\n\
         axiom 张三是好人 : 好人 张三\n  source text \"测试\" locator \"夹具\"\n",
    );
    let output = run(&[format!(":load {}", path.display())]);
    assert_exit(&output, PROVED);
    assert!(stdout(&output).contains("已加载"), "{}", stdout(&output));
}
