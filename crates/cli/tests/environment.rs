//! End-to-end tests for the default legal environment and `std-deduce env`.
//!
//! Repository tests run from the repository root because the fixed
//! `lawpacks/` registry is what they exercise. Temporary-registry tests build
//! their own `lawpacks`, profiles and `std.lock` below a temporary directory and
//! run the CLI with that directory as its working directory. Cargo runs
//! integration tests from `crates/cli`, where no `lawpacks/` exists, so a test
//! that needs the repository registry must say so explicitly.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{build_lock, LOCK_FILE};

const PROVED: i32 = 0;
const LOAD_FAILED: i32 = 1;
const ERROR: i32 = 2;

const GOOD_THEORY: &str = "sort 公民\npred 好人 : 公民 → Prop\nobj 张三 : 公民\naxiom 张三是好人 : 好人 张三\n  source text \"测试\" locator \"夹具\"\n";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn example(name: &str) -> String {
    let path = repo_root().join("examples").join(name);
    assert!(path.is_file(), "missing example file: {}", path.display());
    path.to_string_lossy().into_owned()
}

fn args(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_owned()).collect()
}

fn run_in(current_dir: &Path, arguments: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(arguments)
        .output()
        .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
}

fn run_repl_in(current_dir: &Path, arguments: &[String], input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(arguments)
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

/// Assert the exit code and that stdout contains every needle.
fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
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
    output
}

fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
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
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

fn theory(namespace: &str) -> String {
    format!(
        r#"
namespace {namespace}
sort {namespace}.公民
sort {namespace}.住宅
pred {namespace}.非法搜查 : {namespace}.公民 → {namespace}.住宅 → Prop
pred {namespace}.不受侵犯 : {namespace}.公民 → {namespace}.住宅 → Prop
rule {namespace}.非法搜查即侵犯 :
  params p : {namespace}.公民, h : {namespace}.住宅
  premise {namespace}.非法搜查 p h
  conclude {namespace}.不受侵犯 p h
  source text "测试" locator "一"
"#
    )
}

fn theory_importing(namespace: &str, imported: &str) -> String {
    format!("import {imported}\n{}", theory(namespace))
}

fn facts_case(namespace: &str, imports: &[&str]) -> String {
    let mut text = String::new();
    for import in imports {
        text.push_str(&format!("import {import}\n"));
    }
    text.push_str(&format!(
        "obj 张三 : {namespace}.公民\nobj 甲宅 : {namespace}.住宅\n\
         axiom 事实 : {namespace}.非法搜查 张三 甲宅\n  source text \"案件\" locator \"一\"\n"
    ));
    text
}

fn profile_text(name: &str, trust: Option<&str>, packs: &[(&str, &str)]) -> String {
    let mut text = format!("name = \"{name}\"\ndefault = true\n");
    if let Some(trust) = trust {
        text.push_str(&format!("trust = \"{trust}\"\n"));
    }
    for (pack, version) in packs {
        text.push_str(&format!(
            "\n[[packs]]\nname = \"{pack}\"\nversion = \"{version}\"\n"
        ));
    }
    text
}

// ---------------------------------------------------------------------------
// The repository's official environment
// ---------------------------------------------------------------------------

#[test]
fn env_reports_the_default_profile_and_its_official_pack() {
    let output = check(
        run_in(&repo_root(), &args(&["env"])),
        PROVED,
        &[
            "环境 profile：cn.default",
            "中国法默认环境：只含官方宪法包",
            "  信任要求：official",
            "  cn.constitution 0.2 → 0.2.0（official，锁 sha256:",
            "注册表：",
            "lawpacks",
            "锁定校验：通过（1 个包）",
            "环境加载：通过（1 个包）",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn env_with_no_default_packs_reports_disabled_and_still_checks_the_lock() {
    let output = check(
        run_in(&repo_root(), &args(&["--no-default-packs", "env"])),
        PROVED,
        &[
            "环境 profile：未启用（--no-default-packs）",
            "默认包：未加载",
            "锁定校验：通过（1 个包）",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn env_accepts_the_cn_alias() {
    let output = check(
        run_in(&repo_root(), &args(&["--profile", "cn", "env"])),
        PROVED,
        &["环境 profile：cn.default", "  cn.constitution 0.2 → 0.2.0"],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn env_rejects_an_unknown_profile_and_lists_the_available_ones() {
    let output = check_stderr(
        run_in(
            &repo_root(),
            &args(&["--profile", "no-such-profile", "env"]),
        ),
        ERROR,
        &["no-such-profile", "cn.default"],
    );
    assert!(stdout(&output).is_empty(), "{}", stdout(&output));
}

#[test]
fn the_facts_only_example_proves_under_the_default_environment() {
    let output = check(
        run_in(
            &repo_root(),
            &args(&[
                example("宪法第三十九条-默认环境.std").as_str(),
                ":why cn.constitution.住宅受侵犯 张三 甲宅",
            ]),
        ),
        PROVED,
        &[
            "默认环境 cn.default：已加载 1 个包",
            "  cn.constitution@0.2.0（official）",
            "推导已通过独立校验。",
        ],
    );
    let out = stdout(&output);
    let preload = out
        .find("默认环境 cn.default")
        .unwrap_or_else(|| panic!("no preload line:\n{out}"));
    let report = out
        .find("已加载 `")
        .unwrap_or_else(|| panic!("no load report:\n{out}"));
    assert!(preload < report, "the preload lines come first:\n{out}");
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn no_default_packs_fails_the_facts_only_example_with_a_pack_hint() {
    let output = check_stderr(
        run_in(
            &repo_root(),
            &args(&[
                "--no-default-packs",
                example("宪法第三十九条-默认环境.std").as_str(),
                ":why cn.constitution.住宅受侵犯 张三 甲宅",
            ]),
        ),
        LOAD_FAILED,
        &[
            "未知名称",
            "cn.constitution.人",
            "提示：",
            "cn.constitution",
            "--no-default-packs",
            "import cn.constitution",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("默认环境"),
        "a closed environment prints no preload line:\n{out}"
    );
    assert!(
        !out.contains("已加载"),
        "a failed load must not report a loaded theory:\n{out}"
    );
}

#[test]
fn a_repl_load_with_no_default_packs_gets_the_same_pack_hint() {
    let input = format!(":load {}\n:quit\n", example("宪法第三十九条-默认环境.std"));
    let output = run_repl_in(&repo_root(), &args(&["--no-default-packs"]), &input);
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(ERROR),
        "a failed :load is a command error\nstdout:\n{out}\nstderr:\n{err}"
    );
    assert!(err.is_empty(), "the REPL reports on stdout:\n{err}");
    assert!(
        out.contains("错误："),
        "the failed load keeps its prefix:\n{out}"
    );
    assert!(
        out.contains("提示：")
            && out.contains("cn.constitution.人")
            && out.contains("cn.constitution")
            && out.contains("import cn.constitution"),
        "the closed-environment hint is appended on stdout:\n{out}"
    );
    assert!(
        !out.contains("默认环境 cn.default"),
        "a closed environment prints no preload line:\n{out}"
    );
}

#[test]
fn a_file_that_fails_after_environment_preparation_prints_no_preload_lines() {
    let temp = TempDir::new("file-fails-after-env");
    let file = temp.write("bad.std", "obj 张三 : cn.constitution.不存在\n");
    let path = file.display().to_string();
    let output = check_stderr(
        run_in(&repo_root(), &args(&[path.as_str()])),
        LOAD_FAILED,
        &["未知名称"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("默认环境"),
        "a failed file load must not claim the environment loaded:\n{out}"
    );
    assert!(
        !out.contains("已加载"),
        "a failed file load prints no report:\n{out}"
    );
}

#[test]
fn a_repl_retry_prints_the_preload_lines_only_once() {
    let temp = TempDir::new("repl-preload-once");
    let bad = temp.write("bad.std", "obj 张三 : cn.constitution.不存在\n");
    let input = format!(
        ":load {}\n:load {}\n:quit\n",
        bad.display(),
        example("宪法第三十九条-默认环境.std")
    );
    let output = run_repl_in(&repo_root(), &[], &input);
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(ERROR),
        "the failed first :load keeps the worst exit code\nstdout:\n{out}\nstderr:\n{err}"
    );
    assert_eq!(
        out.matches("默认环境 cn.default").count(),
        1,
        "the failed attempt discards its report; only the successful load prints it:\n{out}"
    );
    assert!(out.contains("已加载 `"), "the second load succeeds:\n{out}");
}

#[test]
fn an_imported_pack_gets_no_missing_pack_hint() {
    let temp = TempDir::new("imported-name-no-hint");
    let file = temp.write(
        "bad.std",
        "import cn.constitution\nobj 张三 : cn.constitution.不存在\n",
    );
    let path = file.display().to_string();
    let output = check_stderr(
        run_in(&repo_root(), &args(&["--no-default-packs", path.as_str()])),
        LOAD_FAILED,
        &["未知名称", "cn.constitution.不存在"],
    );
    let err = stderr(&output);
    assert!(
        !err.contains("提示：") && !err.contains("请写 `import"),
        "an already imported pack is not a missing environment pack:\n{err}"
    );
}

#[test]
fn a_missing_name_inside_a_profile_dependency_is_named_in_the_hint() {
    let temp = TempDir::new("dependency-hint");
    temp.write_pack("pkg.b", "0.1.0", "official", &theory("pkg.b"));
    temp.write_pack(
        "pkg.a",
        "0.1.0",
        "official",
        &theory_importing("pkg.a", "pkg.b"),
    );
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.a", "0.1")]),
    );
    temp.lock();

    let file = temp.write("bad.std", "obj 张三 : pkg.b.公民\n");
    let path = file.display().to_string();
    let output = check_stderr(
        run_in(temp.path(), &args(&["--no-default-packs", path.as_str()])),
        LOAD_FAILED,
        &["提示：", "可能来自法律包 `pkg.b`", "import pkg.b"],
    );
    let err = stderr(&output);
    assert!(
        err.contains("--no-default-packs"),
        "the hint offers removing the flag:\n{err}"
    );
}

#[test]
fn an_unimportable_namespace_pack_gets_no_import_hint() {
    let temp = TempDir::new("nonimportable-namespace");
    temp.write_pack_with_namespace(
        "pkg.shadow",
        "0.1.0",
        "official",
        Some("pkg.a.b"),
        &theory("pkg.a.b"),
    );
    let file = temp.write("bad.std", "obj 张三 : pkg.a.b.不存在\n");
    let path = file.display().to_string();
    let output = check_stderr(
        run_in(temp.path(), &args(&["--no-default-packs", path.as_str()])),
        LOAD_FAILED,
        &["未知名称", "pkg.a.b.不存在"],
    );
    let err = stderr(&output);
    assert!(
        !err.contains("提示："),
        "a pack whose namespace differs from its name cannot be imported:\n{err}"
    );
    assert!(
        !err.contains("import pkg.shadow"),
        "never suggest an import that must fail:\n{err}"
    );
}

#[test]
fn a_pack_without_a_namespace_gets_no_import_hint() {
    let temp = TempDir::new("no-namespace-hint");
    temp.write_pack_with_namespace("pkg.bare", "0.1.0", "official", None, &theory("pkg.bare"));
    let file = temp.write("bad.std", "obj 张三 : pkg.bare.不存在\n");
    let path = file.display().to_string();
    let output = check_stderr(
        run_in(temp.path(), &args(&["--no-default-packs", path.as_str()])),
        LOAD_FAILED,
        &["未知名称", "pkg.bare.不存在"],
    );
    let err = stderr(&output);
    assert!(
        !err.contains("提示："),
        "a pack without a namespace cannot be imported:\n{err}"
    );
    assert!(
        !err.contains("import pkg.bare"),
        "never suggest an import that must fail:\n{err}"
    );
}

#[test]
fn an_importable_prefix_is_not_shadowed_by_a_longer_unimportable_namespace() {
    let temp = TempDir::new("no-namespace-shadowing");
    temp.write_pack("pkg.a", "0.1.0", "official", &theory("pkg.a"));
    temp.write_pack_with_namespace(
        "pkg.shadow",
        "0.1.0",
        "official",
        Some("pkg.a.b"),
        &theory("pkg.a.b"),
    );
    let file = temp.write("bad.std", "obj 张三 : pkg.a.b.不存在\n");
    let path = file.display().to_string();
    let output = check_stderr(
        run_in(temp.path(), &args(&["--no-default-packs", path.as_str()])),
        LOAD_FAILED,
        &["提示：", "可能来自法律包 `pkg.a`"],
    );
    let err = stderr(&output);
    assert!(
        !err.contains("pkg.shadow"),
        "an unimportable namespace must not shadow the importable pkg.a:\n{err}"
    );
}

#[test]
fn a_query_error_gets_no_missing_pack_hint() {
    let output = check_stderr(
        run_in(
            &repo_root(),
            &args(&["--no-default-packs", ":why cn.constitution.不存在 张三"]),
        ),
        ERROR,
        &["未知名称"],
    );
    assert!(
        !stderr(&output).contains("提示："),
        "the hint is only for failed file loads:\n{}",
        stderr(&output)
    );
}

#[test]
fn an_explicit_import_still_works_with_no_default_packs() {
    let output = check(
        run_in(
            &repo_root(),
            &args(&[
                "--no-default-packs",
                example("宪法第三十九条-导入包.std").as_str(),
                ":why cn.constitution.住宅受侵犯 张三 甲宅",
            ]),
        ),
        PROVED,
        &["导入 cn.constitution", "推导已通过独立校验。"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("默认环境"),
        "a closed environment prints no preload line:\n{out}"
    );
}

#[test]
fn invocation_option_errors_are_usage_errors() {
    for (case, arguments, needle) in [
        ("missing profile value", args(&["--profile"]), "--profile"),
        (
            "duplicate profile",
            args(&["--profile", "cn", "--profile", "cn", "env"]),
            "--profile",
        ),
        (
            "profile with no-default-packs",
            args(&["--profile", "cn", "--no-default-packs", "env"]),
            "不能同时",
        ),
        (
            "option after the file",
            args(&[
                example("constitution-39.std").as_str(),
                "--no-default-packs",
            ]),
            "未知选项",
        ),
        (
            "extra argument after env",
            args(&["env", "--no-default-packs"]),
            "env 之前",
        ),
        (
            "help with another option",
            args(&["--profile", "cn", "--help"]),
            "唯一参数",
        ),
        (
            "option after check",
            args(&["check", "--profile", "cn"]),
            "未知选项",
        ),
    ] {
        let output = run_in(&repo_root(), &arguments);
        let code = output.status.code();
        let out = stdout(&output);
        let err = stderr(&output);
        assert_eq!(code, Some(ERROR), "{case}\nstdout:\n{out}\nstderr:\n{err}");
        assert!(
            err.contains(needle),
            "{case}: stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
}

#[test]
fn the_environment_is_not_preloaded_by_startup_or_listing_commands() {
    let output = check(
        run_in(&repo_root(), &args(&[":packs lawpacks"])),
        PROVED,
        &["cn.constitution 0.2.0"],
    );
    assert!(
        !stdout(&output).contains("默认环境"),
        ":packs does not load the default environment:\n{}",
        stdout(&output)
    );

    let output = run_repl_in(&repo_root(), &[], ":inspect\n:packs lawpacks\n:quit\n");
    let code = output.status.code();
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(code, Some(PROVED), "stdout:\n{out}\nstderr:\n{err}");
    assert!(
        !out.contains("默认环境"),
        "a REPL that never loads a file does not preload:\n{out}"
    );
}

// ---------------------------------------------------------------------------
// Temporary registries
// ---------------------------------------------------------------------------

#[test]
fn the_default_environment_loads_only_the_packs_in_its_profile() {
    let temp = TempDir::new("profile-only-official");
    temp.write_pack("pkg.official", "0.1.0", "official", &theory("pkg.official"));
    temp.write_pack(
        "pkg.community",
        "0.1.0",
        "community",
        &theory("pkg.community"),
    );
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.official", "0.1")]),
    );
    temp.lock();

    let output = check(
        run_in(temp.path(), &args(&["env"])),
        PROVED,
        &[
            "环境 profile：cn.default",
            "  pkg.official 0.1 → 0.1.0（official，锁 sha256:",
            "锁定校验：通过（2 个包）",
            "环境加载：通过（1 个包）",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("pkg.community"),
        "a pack outside the profile must not be listed:\n{out}"
    );

    let case = temp.write("case.std", &facts_case("pkg.official", &[]));
    let case_path = case.display().to_string();
    let output = check(
        run_in(temp.path(), &args(&[case_path.as_str(), ":inspect"])),
        PROVED,
        &["pkg.official.非法搜查即侵犯"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("pkg.community"),
        "the default environment must not load declarations from a pack outside the profile:\n{out}"
    );
}

#[test]
fn an_explicit_import_outside_the_profile_is_marked() {
    let temp = TempDir::new("outside-marker");
    temp.write_pack("pkg.official", "0.1.0", "official", &theory("pkg.official"));
    temp.write_pack(
        "pkg.community",
        "0.1.0",
        "community",
        &theory("pkg.community"),
    );
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.official", "0.1")]),
    );
    temp.lock();

    let case = temp.write("case.std", &facts_case("pkg.community", &["pkg.community"]));
    let output = check(
        run_in(
            temp.path(),
            &args(&[
                case.display().to_string().as_str(),
                ":why pkg.community.不受侵犯 张三 甲宅",
            ]),
        ),
        PROVED,
        &[
            "默认环境 cn.default：已加载 1 个包",
            "  导入 pkg.community（环境外：community）",
            "推导已通过独立校验。",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn a_community_pack_inside_the_profile_needs_the_allow_flag() {
    let temp = TempDir::new("community-profile");
    temp.write_pack(
        "pkg.community",
        "0.1.0",
        "community",
        &theory("pkg.community"),
    );
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.community", "0.1")]),
    );
    temp.lock();

    check_stderr(
        run_in(temp.path(), &args(&["env"])),
        ERROR,
        &[
            "cn.default",
            "pkg.community",
            "official",
            "community",
            "--allow-community-packs",
        ],
    );

    let output = check(
        run_in(temp.path(), &args(&["--allow-community-packs", "env"])),
        PROVED,
        &[
            "环境 profile：cn.default",
            "  pkg.community 0.1 → 0.1.0（community",
            "环境加载：通过（1 个包）",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));

    let case = temp.write("case.std", &facts_case("pkg.community", &[]));
    let case_path = case.display().to_string();
    check_stderr(
        run_in(
            temp.path(),
            &args(&[case_path.as_str(), ":why pkg.community.不受侵犯 张三 甲宅"]),
        ),
        LOAD_FAILED,
        &["信任级别", "pkg.community", "--allow-community-packs"],
    );
    check(
        run_in(
            temp.path(),
            &args(&[
                "--allow-community-packs",
                case_path.as_str(),
                ":why pkg.community.不受侵犯 张三 甲宅",
            ]),
        ),
        PROVED,
        &["（已允许非官方包）", "推导已通过独立校验。"],
    );
}

#[test]
fn env_loads_the_profiles_theory_files_and_reports_bad_ones() {
    let temp = TempDir::new("bad-profile-theory");
    temp.write_pack(
        "pkg.official",
        "0.1.0",
        "official",
        "namespace pkg.official\nbogus\n",
    );
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.official", "0.1")]),
    );
    temp.lock();

    let output = check_stderr(
        run_in(temp.path(), &args(&["env"])),
        ERROR,
        &["theory.std", "bogus"],
    );
    assert!(stdout(&output).is_empty(), "{}", stdout(&output));
}

#[test]
fn a_profile_version_mismatch_names_the_constraint_and_manifest_version() {
    let temp = TempDir::new("version-mismatch");
    temp.write_pack("pkg.official", "0.1.0", "official", &theory("pkg.official"));
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.official", "0.2")]),
    );
    temp.lock();

    check_stderr(
        run_in(temp.path(), &args(&["env"])),
        ERROR,
        &["pkg.official", "0.2", "0.1.0"],
    );
}

#[test]
fn a_profile_that_names_a_missing_pack_reports_it_with_the_registry_path() {
    let temp = TempDir::new("missing-profile-pack");
    fs::create_dir_all(temp.lawpacks()).unwrap();
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.missing", "0.1")]),
    );
    temp.lock();

    let output = check_stderr(
        run_in(temp.path(), &args(&["env"])),
        ERROR,
        &[
            "pkg.missing",
            temp.lawpacks().display().to_string().as_str(),
        ],
    );
    assert!(stdout(&output).is_empty(), "{}", stdout(&output));
}

#[test]
fn a_profile_dependency_is_part_of_the_environment_closure() {
    let temp = TempDir::new("dependency-closure");
    temp.write_pack("pkg.b", "0.1.0", "official", &theory("pkg.b"));
    temp.write_pack(
        "pkg.a",
        "0.1.0",
        "official",
        &theory_importing("pkg.a", "pkg.b"),
    );
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.a", "0.1")]),
    );
    temp.lock();

    let output = check(
        run_in(temp.path(), &args(&["env"])),
        PROVED,
        &[
            "  pkg.a 0.1 → 0.1.0（official，锁 sha256:",
            "  pkg.b → 0.1.0（official，依赖）",
            "环境加载：通过（2 个包）",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));

    // A dependency is still inside the environment: importing it explicitly
    // does not make it "outside".
    let case = temp.write("case.std", &facts_case("pkg.b", &["pkg.b"]));
    let output = check(
        run_in(
            temp.path(),
            &args(&[
                case.display().to_string().as_str(),
                ":why pkg.b.不受侵犯 张三 甲宅",
            ]),
        ),
        PROVED,
        &[
            "默认环境 cn.default：已加载 2 个包",
            "  pkg.b@0.1.0（official，依赖）",
            "  导入 pkg.b",
            "推导已通过独立校验。",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("环境外"),
        "a profile dependency is inside the environment:\n{out}"
    );
}

#[test]
fn a_bad_profile_fails_batch_loads_and_env() {
    let temp = TempDir::new("bad-profile");
    temp.write_pack("pkg.official", "0.1.0", "official", &theory("pkg.official"));
    temp.lock();
    temp.write_profile(
        "cn.default.toml",
        "name = \"cn.default\"\ndefault = true\nunexpected = true\n",
    );

    let output = check_stderr(
        run_in(temp.path(), &args(&["env"])),
        ERROR,
        &["cn.default.toml", "unexpected"],
    );
    assert!(stdout(&output).is_empty(), "{}", stdout(&output));

    let file = temp.write("logic.std", GOOD_THEORY);
    let file_path = file.display().to_string();
    let output = check_stderr(
        run_in(temp.path(), &args(&[file_path.as_str()])),
        LOAD_FAILED,
        &["cn.default.toml"],
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "a profile error is a failed load:\n{}",
        stdout(&output)
    );

    // An explicit `:load` command reports the same environment failure as a
    // command error (`2`), not as a batch load failure (`1`).
    let output = check_stderr(
        run_in(temp.path(), &args(&[format!(":load {file_path}").as_str()])),
        ERROR,
        &["错误：", "cn.default.toml"],
    );
    assert!(!stdout(&output).contains("已加载"), "{}", stdout(&output));
}

#[test]
fn a_changed_pack_fails_the_environment_load_before_any_report() {
    let temp = TempDir::new("changed-pack");
    temp.write_pack("pkg.official", "0.1.0", "official", &theory("pkg.official"));
    temp.write_profile(
        "cn.default.toml",
        &profile_text("cn.default", None, &[("pkg.official", "0.1")]),
    );
    temp.lock();

    let theory_path = temp.lawpacks().join("pkg.official/theory.std");
    let mut text = fs::read_to_string(&theory_path).expect("read the copied pack");
    text.push_str("\n-- 改动：破坏锁哈希\n");
    fs::write(&theory_path, text).expect("write the changed pack");

    let case = temp.write("case.std", &facts_case("pkg.official", &[]));
    let output = check_stderr(
        run_in(temp.path(), &args(&[case.display().to_string().as_str()])),
        LOAD_FAILED,
        &["哈希不符"],
    );
    let out = stdout(&output);
    assert!(!out.contains("已加载"), "{out}");
    assert!(!out.contains("默认环境"), "{out}");
}

#[test]
fn a_registry_without_a_default_profile_does_not_open_it_on_load() {
    let temp = TempDir::new("no-default");
    temp.write_pack("pkg.official", "0.1.0", "official", &theory("pkg.official"));
    temp.write_profile(
        "p.other.toml",
        &profile_text("p.other", None, &[("pkg.official", "0.1")])
            .replace("default = true", "default = false"),
    );

    // There is no std.lock. A batch load must not open the registry just
    // because `lawpacks/` exists; only `env` reports the missing lock.
    let file = temp.write("logic.std", GOOD_THEORY);
    let output = check(
        run_in(temp.path(), &args(&[file.display().to_string().as_str()])),
        PROVED,
        &["已加载"],
    );
    let err = stderr(&output);
    assert!(err.is_empty(), "no registry was opened:\n{err}");
    assert!(!stdout(&output).contains("默认环境"), "{}", stdout(&output));

    check_stderr(run_in(temp.path(), &args(&["env"])), ERROR, &["std.lock"]);

    temp.lock();
    let output = check(
        run_in(temp.path(), &args(&["env"])),
        PROVED,
        &[
            "环境 profile：未启用（没有 default = true 的 profile）",
            "默认包：未加载",
            "锁定校验：通过（1 个包）",
        ],
    );
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn env_requires_a_lawpacks_directory() {
    let temp = TempDir::new("env-no-registry");
    let output = check_stderr(
        run_in(temp.path(), &args(&["env"])),
        ERROR,
        &["lawpacks", temp.path().display().to_string().as_str()],
    );
    assert!(stdout(&output).is_empty(), "{}", stdout(&output));
}

#[test]
fn a_directory_without_lawpacks_keeps_pure_logic_files_working() {
    let temp = TempDir::new("no-lawpacks");
    let file = temp.write("logic.std", GOOD_THEORY);
    let output = check(
        run_in(temp.path(), &args(&[file.display().to_string().as_str()])),
        PROVED,
        &["已加载"],
    );
    assert!(!stdout(&output).contains("默认环境"), "{}", stdout(&output));
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-environment-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempDir { path }
    }

    fn path(&self) -> &Path {
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

    fn write_pack(&self, name: &str, version: &str, trust: &str, theory: &str) -> PathBuf {
        self.write_pack_with_namespace(name, version, trust, Some(name), theory)
    }

    fn write_pack_with_namespace(
        &self,
        name: &str,
        version: &str,
        trust: &str,
        namespace: Option<&str>,
        theory: &str,
    ) -> PathBuf {
        let dir = self.lawpacks().join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        let mut manifest = format!(
            "[pack]\nname = \"{name}\"\nversion = \"{version}\"\n\
             jurisdiction = \"CN\"\nterritory = \"CN\"\n"
        );
        if let Some(namespace) = namespace {
            manifest.push_str(&format!("namespace = \"{namespace}\"\n"));
        }
        manifest.push_str(&format!(
            "trust = \"{trust}\"\n\n[[files]]\npath = \"theory.std\"\nkind = \"theory\"\n"
        ));
        fs::write(dir.join("lawpack.toml"), manifest)
            .unwrap_or_else(|error| panic!("write manifest: {error}"));
        fs::write(dir.join("theory.std"), theory)
            .unwrap_or_else(|error| panic!("write theory: {error}"));
        dir
    }

    fn write_profile(&self, name: &str, text: &str) -> PathBuf {
        self.write(&format!("lawpacks/profiles/{name}"), text)
    }

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
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
