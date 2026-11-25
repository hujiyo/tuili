//! End-to-end tests for the closed environment and case extensions.
//!
//! Every case runs the CLI from the repository root, so the fixed `lawpacks/`
//! registry supplies `cn.constitution`. Temporary case files live in their own
//! directory outside the repository and are removed when the test ends.

use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_cert::{Certificate, ObligationKind};

const PROVED: i32 = 0;
const LOAD_FAILED: i32 = 1;
const GAP: i32 = 1;
const ERROR: i32 = 2;

/// The case rule the Sun Zhigang example declares and the certificate must name.
const CASE_RULE: &str = "省人大法工委解释";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn example(name: &str) -> String {
    let path = repo_root().join("examples").join(name);
    assert!(path.is_file(), "missing example file: {}", path.display());
    path.to_string_lossy().into_owned()
}

fn sun_zhigang() -> String {
    example("宪法案例-孙志刚.std")
}

fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_in(current_dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_with_stdin(args: &[String], input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"));
    child
        .stdin
        .take()
        .expect("stdin is piped")
        .write_all(input.as_bytes())
        .expect("write REPL input");
    child
        .wait_with_output()
        .unwrap_or_else(|error| panic!("failed to wait for the CLI: {error}"))
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

/// Assert the exit code and that stdout contains every needle.
fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
    assert_exit(&output, expected);
    let out = stdout(&output);
    let err = stderr(&output);
    for needle in needles {
        assert!(
            out.contains(needle),
            "stdout does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

/// Assert the exit code and that stderr contains every needle.
fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
    assert_exit(&output, expected);
    let out = stdout(&output);
    let err = stderr(&output);
    for needle in needles {
        assert!(
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

/// The certificate JSON the `:cert` command printed after its load report.
fn certificate_json(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    text[start..].trim_end().to_owned()
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-closed-env-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn write(&self, name: &str, contents: &str) -> PathBuf {
        let path = self.path.join(name);
        fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

// ---------------------------------------------------------------------------
// The closed environment refuses case declarations
// ---------------------------------------------------------------------------

#[test]
fn closed_env_rejects_a_case_predicate() {
    let temp = TempDir::new("reject-pred");
    let file = temp.write(
        "case.std",
        "import cn.constitution\npred 恶意侵占 : cn.constitution.人 → Prop\n",
    );
    let path = file.display().to_string();

    let output = check_stderr(
        run(&["--closed-env".to_owned(), path]),
        LOAD_FAILED,
        &[
            "封闭环境",
            "恶意侵占",
            "--allow-case-rules",
            "案件文件只能 import 法律包",
        ],
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "a rejected case must not be loaded:\n{}",
        stdout(&output)
    );
}

#[test]
fn closed_env_rejects_every_case_declaration_kind() {
    let mut def = String::from("pred 恶意侵占 : cn.constitution.人 → Prop\n");
    def.push_str(
        "def 恶意概念 : cn.constitution.人 → Prop := λ (x : cn.constitution.人) := 恶意侵占 x\n",
    );
    let mut rule = String::from("rule 恶意取得 :\n");
    rule.push_str("  params x : cn.constitution.人\n");
    rule.push_str("  premise cn.constitution.中国国籍 x\n");
    rule.push_str("  conclude cn.constitution.公民 x\n");
    rule.push_str("  burden claimant\n");
    rule.push_str("  standard preponderance\n");
    rule.push_str("  source text \"案情\" locator \"测试\"\n");
    let mut contrary = String::from("pred 恶意左 : cn.constitution.人 → Prop\n");
    contrary.push_str("pred 恶意右 : cn.constitution.人 → Prop\ncontrary 恶意左 恶意右\n");
    let mut unique = String::from("pred 恶意应适用 : cn.constitution.人 → Prop\n");
    unique.push_str("unique 恶意应适用 1\n");
    let mut interpretation = String::from("obj 张三 : cn.constitution.人\n");
    interpretation.push_str(
        "interpret 恶意解释 : cn.constitution.中国国籍 张三 → cn.constitution.公民 张三\n\
         \x20 direction literal\n  source text \"测试\" locator \"一\" version \"2020\"\n",
    );

    let cases = [
        ("sort", "sort 恶意类型\n".to_owned()),
        (
            "pred",
            "pred 恶意侵占 : cn.constitution.人 → Prop\n".to_owned(),
        ),
        ("def", def),
        ("rule", rule),
        ("contrary", contrary),
        ("unique", unique),
        ("interpret", interpretation),
    ];
    for (kind, declarations) in cases {
        let temp = TempDir::new(&format!("reject-{kind}"));
        let path = temp
            .write(
                "case.std",
                &format!("import cn.constitution\n{declarations}"),
            )
            .display()
            .to_string();

        let output = check_stderr(
            run(&["--closed-env".to_owned(), path.clone()]),
            LOAD_FAILED,
            &["封闭环境", "--allow-case-rules"],
        );
        assert!(
            !stdout(&output).contains("已加载"),
            "{kind}: a rejected case must not be loaded:\n{}",
            stdout(&output)
        );

        // The same file loads once the author opts in explicitly.
        let output = run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
        ]);
        check(output, PROVED, &["已加载"]);
    }
}

#[test]
fn the_declaration_list_is_truncated_after_eight_items() {
    let temp = TempDir::new("truncated");
    let mut source = String::from("import cn.constitution\n");
    for index in 1..=9 {
        source.push_str(&format!("sort 恶意类型{index}\n"));
    }
    let path = temp.write("case.std", &source).display().to_string();

    let output = check_stderr(
        run(&["--closed-env".to_owned(), path]),
        LOAD_FAILED,
        &["`sort 恶意类型8`", "等 9 项", "封闭环境"],
    );
    let err = stderr(&output);
    assert!(
        !err.contains("`sort 恶意类型9`"),
        "only the first eight declarations are listed:\n{err}"
    );
}

// ---------------------------------------------------------------------------
// The closed environment accepts facts-only cases
// ---------------------------------------------------------------------------

#[test]
fn closed_env_accepts_a_facts_only_case() {
    let output = check(
        run(&[
            "--closed-env".to_owned(),
            example("宪法案例-齐玉苓.std"),
            ":why cn.constitution.受教育权 齐玉苓".to_owned(),
            ":inspect".to_owned(),
        ]),
        PROVED,
        &["已加载", "推导已通过独立校验。"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("[案件扩展]"),
        "a facts-only case declares no extension:\n{out}"
    );
}

#[test]
fn closed_env_rejects_a_module_file() {
    let temp = TempDir::new("module");
    let path = temp
        .write(
            "module.std",
            "namespace evil.module\nsort evil.module.恶意类型\n",
        )
        .display()
        .to_string();

    check_stderr(
        run(&["--closed-env".to_owned(), path.clone()]),
        LOAD_FAILED,
        &["只接受案件文件", "namespace", "import 加载"],
    );
    // The opt-in only lifts the declaration check: a module is still refused.
    check_stderr(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
        ]),
        LOAD_FAILED,
        &["只接受案件文件"],
    );
}

// ---------------------------------------------------------------------------
// Case-local rules are marked as extensions
// ---------------------------------------------------------------------------

#[test]
fn case_extensions_accumulate_and_survive_a_failed_load() {
    let temp = TempDir::new("accumulate");
    let second = temp.write(
        "second.std",
        "import cn.constitution\npred 第二扩展 : cn.constitution.人 → Prop\n",
    );
    let bad = temp.write(
        "bad.std",
        "import cn.constitution\npred 第三扩展 : 不存在 → Prop\n",
    );
    let input = format!(
        ":load {}\n:load {}\n:inspect\n:load {}\n:inspect\n:quit\n",
        sun_zhigang(),
        second.display(),
        bad.display()
    );
    let output = run_with_stdin(
        &["--closed-env".to_owned(), "--allow-case-rules".to_owned()],
        &input,
    );
    // The failed second `:load` is a command error in the REPL.
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    assert!(
        out.contains("  sort  法源 : Type [案件扩展]"),
        "the first case's extension stays marked:\n{out}"
    );
    assert!(
        out.contains("  pred  第二扩展 : cn.constitution.人 → Prop [案件扩展]"),
        "a later successful load adds its own extension:\n{out}"
    );
    assert!(
        !out.lines()
            .any(|line| line.trim_start().starts_with("pred  第三扩展")),
        "a file rejected by the loader records no extension:\n{out}"
    );
}

#[test]
fn only_the_case_rules_a_proof_used_are_recorded() {
    // The local rule can never fire (nothing proves 局部谓词), so a certificate
    // for a pack-only goal must not carry a local-extension obligation.
    let temp = TempDir::new("unused-rule");
    let path = temp
        .write(
            "case.std",
            "import cn.constitution\n\n\
             obj 甲 : cn.constitution.人\n\n\
             axiom 甲有中国国籍 : cn.constitution.中国国籍 甲\n  source text \"案情\" locator \"身份\"\n\n\
             pred 局部谓词 : cn.constitution.人 → Prop\n\n\
             rule 局部规则 :\n  params x : cn.constitution.人\n  premise 局部谓词 x\n\
             conclude cn.constitution.言论自由 x\n  source text \"案情\" locator \"测试\"\n",
        )
        .display()
        .to_string();

    let output = run(&[
        "--closed-env".to_owned(),
        "--allow-case-rules".to_owned(),
        path.clone(),
        ":cert cn.constitution.公民 甲".to_owned(),
    ]);
    assert_exit(&output, PROVED);
    let json = certificate_json(&output);
    let certificate = Certificate::from_json(&json).expect("the certificate JSON parses");
    assert!(
        certificate.open_obligations.is_empty(),
        "an unused case rule adds no obligation: {:?}",
        certificate.open_obligations
    );

    let output = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
            ":why cn.constitution.公民 甲".to_owned(),
        ]),
        PROVED,
        &["推导已通过独立校验。"],
    );
    assert!(
        !stdout(&output).contains("本地扩展："),
        "an unused case rule prints no extension line:\n{}",
        stdout(&output)
    );
}

#[test]
fn closed_env_rejects_facts_that_invent_a_concept_in_their_type() {
    let cases: &[(&str, &str, &str, &str)] = &[
        (
            "obj-function-type",
            "obj 恶意 : cn.constitution.人 → Prop\n",
            "obj 恶意",
            "sort",
        ),
        ("obj-prop", "obj 法律命题 : Prop\n", "obj 法律命题", "sort"),
        ("obj-type", "obj 新类型 : Type\n", "obj 新类型", "sort"),
        (
            "axiom-prop",
            "axiom 法律命题 : Prop\n  source text \"案情\" locator \"测试\"\n",
            "axiom 法律命题",
            "类型必须是命题",
        ),
        (
            "axiom-function-type",
            "axiom 恶意 : cn.constitution.人 → Prop\n  source text \"案情\" locator \"测试\"\n",
            "axiom 恶意",
            "类型必须是命题",
        ),
    ];
    for (tag, declarations, declared, reason) in cases {
        let temp = TempDir::new(tag);
        let path = temp
            .write(
                "case.std",
                &format!("import cn.constitution\n{declarations}"),
            )
            .display()
            .to_string();

        let output = check_stderr(
            run(&["--closed-env".to_owned(), path.clone()]),
            LOAD_FAILED,
            &["封闭环境", declared, reason, "--allow-case-rules"],
        );
        assert!(
            !stdout(&output).contains("已加载"),
            "{tag}: a rejected case must not be loaded:\n{}",
            stdout(&output)
        );

        // With the explicit opt-in the same declarations are case extensions.
        check(
            run(&[
                "--closed-env".to_owned(),
                "--allow-case-rules".to_owned(),
                path,
            ]),
            PROVED,
            &["已加载"],
        );
    }
}

/// The P0 reproduction: an object of a function type plus a fact about it.
#[test]
fn closed_env_rejects_a_concept_built_from_an_object_type() {
    let temp = TempDir::new("obj-concept");
    let path = temp
        .write(
            "case.std",
            "import cn.constitution\n\n\
             obj 甲 : cn.constitution.人\n\
             obj 恶意 : cn.constitution.人 → Prop\n\n\
             axiom 甲恶意 : 恶意 甲\n  source text \"案情\" locator \"测试\"\n",
        )
        .display()
        .to_string();

    check_stderr(
        run(&["--closed-env".to_owned(), path]),
        LOAD_FAILED,
        &["obj 恶意", "类型必须是已加载法律包里的 sort"],
    );
}

#[test]
fn plain_objects_and_facts_are_still_accepted() {
    let temp = TempDir::new("plain-facts");
    let path = temp
        .write(
            "case.std",
            "import cn.constitution\n\n\
             obj 甲 : cn.constitution.人\n\n\
             axiom 甲有中国国籍 : cn.constitution.中国国籍 甲\n  source text \"案情\" locator \"测试\"\n",
        )
        .display()
        .to_string();

    check(
        run(&["--closed-env".to_owned(), path]),
        PROVED,
        &["已加载", "+ 甲", "+ 甲有中国国籍"],
    );
}

#[test]
fn allow_case_rules_marks_abnormal_objects_and_axioms() {
    let temp = TempDir::new("mark-facts");
    let path = temp
        .write(
            "case.std",
            "import cn.constitution\n\n\
             obj 甲 : cn.constitution.人\n\
             obj 恶意 : cn.constitution.人 → Prop\n\
             obj 新类型 : Type\n\
             obj 命题对象 : Prop\n\n\
             axiom 甲有中国国籍 : cn.constitution.中国国籍 甲\n  source text \"案情\" locator \"身份\"\n\
             axiom 法律命题 : Prop\n  source text \"案情\" locator \"命题\"\n\
             axiom 甲恶意 : 恶意 甲\n  source text \"案情\" locator \"恶意\"\n",
        )
        .display()
        .to_string();

    let output = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
            ":inspect".to_owned(),
        ]),
        PROVED,
        &["已加载"],
    );
    let out = stdout(&output);
    let line = |needle: &str| -> String {
        out.lines()
            .find(|line| line.contains(needle))
            .unwrap_or_else(|| panic!("no `{needle}` line:\n{out}"))
            .to_owned()
    };

    // A plain individual and a fact stated with pack declarations stay
    // unmarked.
    assert!(!line("obj   甲 :").contains("[案件扩展]"), "{out}");
    assert!(
        !line("fact  甲有中国国籍 :").contains("[案件扩展]"),
        "{out}"
    );
    // The abnormal types and the fact built on them are extensions.
    assert!(line("obj   恶意 :").contains("[案件扩展]"), "{out}");
    assert!(line("obj   新类型 :").contains("[案件扩展]"), "{out}");
    assert!(line("obj   命题对象 :").contains("[案件扩展]"), "{out}");
    assert!(line("axiom 法律命题 :").contains("[案件扩展]"), "{out}");
    assert!(line("fact  甲恶意 :").contains("[案件扩展]"), "{out}");
}

#[test]
fn allow_case_rules_marks_local_sorts_and_function_type_axioms() {
    // Without a `pred`, an axiom of a function type is a local predicate, and
    // an object of a sort the case declared is a local individual: neither may
    // look like a plain fact in the ledger.
    let temp = TempDir::new("local-types");
    let path = temp
        .write(
            "case.std",
            "import cn.constitution\n\n\
             sort 本地类型\n\n\
             obj 甲 : 本地类型\n\n\
             axiom 恶意 : cn.constitution.人 → Prop\n  source text \"案情\" locator \"测试\"\n\n\
             obj 张三 : cn.constitution.人\n\n\
             axiom 张三有中国国籍 : cn.constitution.中国国籍 张三\n  source text \"案情\" locator \"身份\"\n",
        )
        .display()
        .to_string();

    let output = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
            ":inspect".to_owned(),
        ]),
        PROVED,
        &["已加载"],
    );
    let out = stdout(&output);
    let line = |needle: &str| -> String {
        out.lines()
            .find(|line| line.contains(needle))
            .unwrap_or_else(|| panic!("no `{needle}` line:\n{out}"))
            .to_owned()
    };
    assert!(
        line("sort  本地类型 :").contains("[案件扩展]"),
        "a case-local sort is an extension:\n{out}"
    );
    assert!(
        line("obj   甲 : 本地类型").contains("[案件扩展]"),
        "an object of a case-local sort is an extension:\n{out}"
    );
    assert!(
        line("axiom 恶意 :").contains("[案件扩展]"),
        "a function-type axiom is a local predicate:\n{out}"
    );
    assert!(
        !line("obj   张三 : cn.constitution.人").contains("[案件扩展]"),
        "an object of a pack sort stays unmarked:\n{out}"
    );
    assert!(
        !line("fact  张三有中国国籍 :").contains("[案件扩展]"),
        "a plain fact stays unmarked:\n{out}"
    );
}

#[test]
fn given_unknown_name_gets_the_closed_hint() {
    let output = check_stderr(
        run(&[
            "--closed-env".to_owned(),
            example("宪法案例-齐玉苓.std"),
            ":given 恶意 甲".to_owned(),
        ]),
        ERROR,
        &[
            "未知名称 `恶意`",
            "已加载的法律包中没有 `恶意`",
            "封闭环境不会为案件补造法律概念",
        ],
    );
    assert!(
        !stdout(&output).contains("已登记用户陈述"),
        "a rejected fact must not enter the ledger:\n{}",
        stdout(&output)
    );
}

#[test]
fn the_default_mode_verifies_a_case_rule_certificate() {
    let generated = run(&[
        "--closed-env".to_owned(),
        "--allow-case-rules".to_owned(),
        sun_zhigang(),
        ":cert 不得收容 孙志刚".to_owned(),
    ]);
    assert_exit(&generated, PROVED);
    let temp = TempDir::new("verify-default");
    let certificate = temp.write("certificate.json", &certificate_json(&generated));

    // The same case file loads without the closed mode, and the certificate
    // still records the obligation it was exported with.
    let output = check(
        run(&[
            sun_zhigang(),
            format!(":verify-cert {}", certificate.display()),
        ]),
        GAP,
        &["环境校验：通过", "需人判断：是", "  本地扩展：", CASE_RULE],
    );
    assert!(
        stdout(&output).contains("逻辑校验：通过"),
        "{}",
        stdout(&output)
    );
}

#[test]
fn cert_and_why_report_the_same_extension_description() {
    let cert_output = run(&[
        "--closed-env".to_owned(),
        "--allow-case-rules".to_owned(),
        sun_zhigang(),
        ":cert 不得收容 孙志刚".to_owned(),
    ]);
    assert_exit(&cert_output, PROVED);
    let json = certificate_json(&cert_output);
    let certificate = Certificate::from_json(&json).expect("the certificate JSON parses");
    let cert_description = certificate
        .open_obligations
        .iter()
        .find(|obligation| obligation.id == "local-extension")
        .unwrap_or_else(|| panic!("no local-extension obligation:\n{json}"))
        .description
        .clone();

    let why_output = run(&[
        "--closed-env".to_owned(),
        "--allow-case-rules".to_owned(),
        sun_zhigang(),
        ":why 不得收容 孙志刚".to_owned(),
    ]);
    assert_exit(&why_output, GAP);
    let out = stdout(&why_output);
    let line = out
        .lines()
        .find(|line| line.starts_with("  本地扩展："))
        .unwrap_or_else(|| panic!("no local-extension line:\n{out}"));
    let why_description = line.trim_start_matches("  本地扩展：");
    assert_eq!(cert_description, why_description);
}

#[test]
fn closed_env_imports_a_community_pack() {
    let root = TempDir::new("community-pack");
    let pack = root.path.join("lawpacks").join("pkg.community");
    fs::create_dir_all(&pack).unwrap();
    fs::write(
        pack.join("lawpack.toml"),
        "[pack]\nname = \"pkg.community\"\nversion = \"0.1.0\"\n\
         jurisdiction = \"CN\"\nterritory = \"CN\"\nnamespace = \"pkg.community\"\n\
         trust = \"community\"\n\n[[files]]\npath = \"theory.std\"\nkind = \"theory\"\n",
    )
    .unwrap();
    fs::write(
        pack.join("theory.std"),
        "namespace pkg.community\nsort pkg.community.人\n\
         pred pkg.community.好人 : pkg.community.人 → Prop\n",
    )
    .unwrap();
    let lockfile = std_deduce_lawpack::build_lock(&root.path.join("lawpacks"))
        .expect("the temporary registry is sound");
    lockfile
        .write(
            &root
                .path
                .join("lawpacks")
                .join(std_deduce_lawpack::LOCK_FILE),
        )
        .expect("write the lock");
    root.write(
        "case.std",
        "import pkg.community\n\nobj 张三 : pkg.community.人\n\n\
         axiom 张三是好人 : pkg.community.好人 张三\n  source text \"案情\" locator \"测试\"\n",
    );

    let output = check(
        run_in(&root.path, &["--closed-env", "case.std", ":inspect"]),
        PROVED,
        &["[pkg.community@0.1.0]"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("[案件扩展]"),
        "pack declarations are not case extensions:\n{out}"
    );
}

#[test]
fn allow_case_rules_marks_the_ledger() {
    let output = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            sun_zhigang(),
            ":inspect".to_owned(),
        ]),
        PROVED,
        &[
            "  sort  法源 : Type [案件扩展]",
            "  pred  应当收容 : cn.constitution.人 → Prop [案件扩展]",
        ],
    );
    let out = stdout(&output);
    let rule_line = out
        .lines()
        .find(|line| line.contains("rule  省人大法工委解释"))
        .unwrap_or_else(|| panic!("no local rule line:\n{out}"));
    assert!(rule_line.contains("[案件扩展]"), "{rule_line}");
    // Facts are not legal concepts: `obj` and `fact` stay unmarked.
    let fact_line = out
        .lines()
        .find(|line| line.contains("fact  孙志刚有中国国籍"))
        .unwrap_or_else(|| panic!("no fact line:\n{out}"));
    assert!(!fact_line.contains("[案件扩展]"), "{fact_line}");
}

#[test]
fn a_case_rule_certificate_records_the_local_extension() {
    let output = run(&[
        "--closed-env".to_owned(),
        "--allow-case-rules".to_owned(),
        sun_zhigang(),
        ":cert 不得收容 孙志刚".to_owned(),
    ]);
    // The root is reachable, so `:cert` still exits `0`; the obligation is
    // what keeps `:why` and `:verify-cert` from claiming an unqualified proof.
    assert_exit(&output, PROVED);

    let json = certificate_json(&output);
    assert!(json.contains("\"id\": \"local-extension\""), "{json}");
    assert!(
        json.contains("\"kind\": \"needs_human_determination\""),
        "{json}"
    );
    assert!(json.contains(CASE_RULE), "{json}");

    let certificate = Certificate::from_json(&json).expect("the certificate JSON parses");
    let obligation = certificate
        .open_obligations
        .iter()
        .find(|obligation| obligation.id == "local-extension")
        .unwrap_or_else(|| panic!("no local-extension obligation:\n{json}"));
    assert_eq!(obligation.kind, ObligationKind::NeedsHumanDetermination);
    assert!(
        obligation.description.contains(CASE_RULE),
        "{}",
        obligation.description
    );
    assert!(
        !obligation.nodes.is_empty(),
        "the obligation names the nodes that applied the rule"
    );
    assert!(
        obligation.nodes.windows(2).all(|pair| pair[0] < pair[1]),
        "node indices are deduplicated and ascending: {:?}",
        obligation.nodes
    );
}

#[test]
fn why_reports_the_local_extension_and_a_gap() {
    let output = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            sun_zhigang(),
            ":why 不得收容 孙志刚".to_owned(),
        ]),
        GAP,
        &[
            "  本地扩展：",
            CASE_RULE,
            "仍有未决义务",
            "不能报告为无保留的证明",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("推导已通过独立校验。"),
        "a case-rule proof is not reported as unqualified:\n{out}"
    );
}

#[test]
fn verify_cert_reports_the_local_extension() {
    let generated = run(&[
        "--closed-env".to_owned(),
        "--allow-case-rules".to_owned(),
        sun_zhigang(),
        ":cert 不得收容 孙志刚".to_owned(),
    ]);
    assert_exit(&generated, PROVED);
    let json = certificate_json(&generated);

    // Checking happens in a fresh session with the same options; the cert
    // records the same environment identity.
    let temp = TempDir::new("verify");
    let certificate = temp.write("certificate.json", &json);
    let output = check(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            sun_zhigang(),
            format!(":verify-cert {}", certificate.display()),
        ]),
        GAP,
        &["环境校验：通过", "需人判断：是", "  本地扩展：", CASE_RULE],
    );
    let out = stdout(&output);
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("内核证明：通过"), "{out}");
    assert!(
        !out.contains("逻辑校验：失败"),
        "the extension is an obligation, not a proof failure:\n{out}"
    );
}

// ---------------------------------------------------------------------------
// Unknown names and the default mode
// ---------------------------------------------------------------------------

#[test]
fn closed_env_hints_at_an_unknown_name() {
    let temp = TempDir::new("unknown");
    let path = temp
        .write(
            "case.std",
            "import cn.constitution\n\nobj 张三 : cn.constitution.人\n\n\
             axiom 张三有恶意 : 恶意侵占 张三\n  source text \"案情\" locator \"测试\"\n",
        )
        .display()
        .to_string();

    let output = check_stderr(
        run(&["--closed-env".to_owned(), path.clone()]),
        LOAD_FAILED,
        &[
            "未知名称 `恶意侵占`",
            "已加载的法律包中没有 `恶意侵占`",
            "封闭环境不会为案件补造法律概念",
            "--allow-case-rules",
        ],
    );
    let err = stderr(&output);
    assert_eq!(
        err.lines().count(),
        2,
        "the hint is appended as one extra line:\n{err:?}"
    );

    // The opt-in variant says the concept is still missing.
    check_stderr(
        run(&[
            "--closed-env".to_owned(),
            "--allow-case-rules".to_owned(),
            path,
        ]),
        LOAD_FAILED,
        &[
            "已加载的法律包中没有 `恶意侵占`",
            "请加载覆盖它的法律包或检查名称拼写",
        ],
    );
}

#[test]
fn the_default_mode_keeps_case_rules_and_marks_nothing() {
    let output = check(
        run(&[
            sun_zhigang(),
            ":inspect".to_owned(),
            ":why 不得收容 孙志刚".to_owned(),
        ]),
        PROVED,
        &["已加载", "推导已通过独立校验。"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("[案件扩展]"),
        "without --closed-env nothing is recorded:\n{out}"
    );
    assert!(
        !out.contains("本地扩展："),
        "without --closed-env the certificate carries no extension:\n{out}"
    );
}

#[test]
fn the_closed_environment_is_not_a_usage_error_on_its_own() {
    let output = run(&[
        "--closed-env".to_owned(),
        "--closed-env".to_owned(),
        example("宪法案例-齐玉苓.std"),
    ]);
    check(output, PROVED, &["已加载"]);
}

#[test]
fn a_case_file_that_fails_without_the_closed_mode_still_fails_with_it() {
    // A facts-only case that references a name no loaded pack defines must not
    // be salvaged by the closed mode; the error keeps its load-failure exit.
    let temp = TempDir::new("closed-unknown");
    let path = temp
        .write(
            "case.std",
            "import cn.constitution\n\n\
             axiom 事实 : 不存在 张三\n  source text \"案情\" locator \"测试\"\n",
        )
        .display()
        .to_string();
    let output = check_stderr(
        run(&["--closed-env".to_owned(), path]),
        LOAD_FAILED,
        &["未知名称"],
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "nothing is committed on a failed load:\n{}",
        stdout(&output)
    );
    assert_eq!(
        output.status.code(),
        Some(LOAD_FAILED),
        "the batch entry stays a load failure, not a usage error ({} vs {ERROR})",
        LOAD_FAILED
    );
}
