//! End-to-end tests for explicit namespaces: module loading, cross-module
//! references, `:inspect` suffixes, and `:why` over qualified names.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const MODULE_A: &str = r#"
namespace a
sort a.公民
sort a.住宅
pred a.非法搜查 : a.公民 → a.住宅 → Prop
pred a.不受侵犯 : a.公民 → a.住宅 → Prop
rule a.非法搜查即侵犯 :
  params p : a.公民, h : a.住宅
  premise a.非法搜查 p h
  conclude a.不受侵犯 p h
  source text "测试" locator "一"
"#;

const MODULE_B: &str = r#"
namespace b
sort b.公民
sort b.住宅
pred b.非法搜查 : b.公民 → b.住宅 → Prop
pred b.不受侵犯 : b.公民 → b.住宅 → Prop
rule b.非法搜查即侵犯 :
  params p : b.公民, h : b.住宅
  premise b.非法搜查 p h
  conclude b.不受侵犯 p h
  source text "测试" locator "一"
"#;

const CASE: &str = r#"
pred 违法 : a.公民 → Prop
obj 张三 : a.公民
obj 甲宅 : a.住宅
obj 李四 : b.公民
obj 乙宅 : b.住宅
axiom 事实 : a.非法搜查 张三 甲宅
  source text "案件" locator "一"
rule 案件规则 :
  params p : a.公民, h : a.住宅
  premise a.非法搜查 p h
  conclude 违法 p
  source text "案件" locator "二"
"#;

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-namespace-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
        TempDir { path }
    }

    fn write(&self, name: &str, source: &str) -> PathBuf {
        let path = self.path.join(name);
        fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn run(commands: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce-cli"))
        .args(commands)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

fn load(path: &Path) -> String {
    format!(":load {}", path.display())
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn line_with<'a>(out: &'a str, needle: &str) -> &'a str {
    out.lines()
        .find(|line| line.contains(needle))
        .unwrap_or_else(|| panic!("no output line contains {needle:?}\n{out}"))
}

fn namespaced_fixture(tag: &str) -> (TempDir, PathBuf, PathBuf, PathBuf) {
    let dir = TempDir::new(tag);
    let a = dir.write("a.std", MODULE_A);
    let b = dir.write("b.std", MODULE_B);
    let case = dir.write("case.std", CASE);
    (dir, a, b, case)
}

#[test]
fn inspect_marks_namespaced_declarations_and_qualified_goals_prove() {
    let (_dir, a, b, case) = namespaced_fixture("inspect");
    let output = run(vec![
        load(&a),
        load(&b),
        load(&case),
        ":inspect".to_string(),
        ":why a.不受侵犯 张三 甲宅".to_string(),
        ":why 违法 张三".to_string(),
    ]);
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(0),
        "expected exit 0, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );

    let a_pred = line_with(&out, "a.非法搜查 :");
    assert!(
        a_pred.trim_end().ends_with("[a]"),
        "a namespaced declaration must show its theory: {a_pred:?}"
    );
    let b_pred = line_with(&out, "b.非法搜查 :");
    assert!(
        b_pred.trim_end().ends_with("[b]"),
        "a namespaced declaration must show its theory: {b_pred:?}"
    );
    let a_rule = line_with(&out, "rule  a.非法搜查即侵犯 :");
    assert!(a_rule.trim_end().ends_with("[a]"), "got: {a_rule:?}");

    let case_pred = line_with(&out, "pred  违法 :");
    assert!(
        !case_pred.contains("[a]") && !case_pred.contains("[b]"),
        "a case declaration must not get a namespace suffix: {case_pred:?}"
    );
    let case_obj = line_with(&out, "obj   张三 :");
    assert!(
        !case_obj.contains("[a]") && !case_obj.contains("[b]"),
        "a case declaration must not get a namespace suffix: {case_obj:?}"
    );

    for needle in [
        "▸ a.不受侵犯 张三 甲宅",
        "▸ 违法 张三",
        "推导已通过独立校验。",
    ] {
        assert!(out.contains(needle), "missing {needle:?}\n{out}");
    }
}

#[test]
fn a_fact_from_one_namespace_does_not_satisfy_another_namespace() {
    let (_dir, a, b, case) = namespaced_fixture("no-cross-talk");
    let output = run(vec![
        load(&a),
        load(&b),
        load(&case),
        ":why b.不受侵犯 李四 乙宅".to_string(),
    ]);
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(1),
        "a b-goal without a b-fact must be a gap, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    assert!(
        out.contains("b.不受侵犯 李四 乙宅"),
        "the gap must name the qualified goal:\n{out}"
    );
    assert!(
        out.contains("缺：b.非法搜查 李四 乙宅"),
        "the missing premise must stay in namespace b:\n{out}"
    );
}

#[test]
fn module_load_order_does_not_change_why_or_cert_results() {
    let (_dir, a, b, case) = namespaced_fixture("order");
    let tail = [
        ":why a.不受侵犯 张三 甲宅".to_string(),
        ":cert a.不受侵犯 张三 甲宅".to_string(),
    ];

    let mut ab = vec![load(&a), load(&b), load(&case)];
    ab.extend(tail.iter().cloned());
    let mut ba = vec![load(&b), load(&a), load(&case)];
    ba.extend(tail.iter().cloned());

    let output_ab = run(ab);
    let output_ba = run(ba);
    let out_ab = stdout(&output_ab);
    let out_ba = stdout(&output_ba);
    assert_eq!(output_ab.status.code(), Some(0));
    assert_eq!(output_ba.status.code(), Some(0));

    fn result(out: &str) -> &str {
        let start = out
            .find("▸ a.不受侵犯")
            .unwrap_or_else(|| panic!("no derivation output:\n{out}"));
        &out[start..]
    }
    assert_eq!(
        result(&out_ab),
        result(&out_ba),
        "swapping module load order changed the `:why` / `:cert` result"
    );
    assert!(result(&out_ab).contains("推导已通过独立校验。"));
}

#[test]
fn a_module_with_an_unqualified_reference_fails_to_load() {
    let dir = TempDir::new("bad-module");
    let bad = dir.write(
        "bad.std",
        "namespace bad\nsort bad.公民\npred bad.P : 公民 → Prop\n",
    );
    let output = run(vec![load(&bad)]);
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(2),
        "an unqualified reference must fail the load, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    assert!(
        err.contains("pred bad.P") && err.contains("公民"),
        "the load error should name the declaration and the unqualified reference:\n{err}"
    );
}
