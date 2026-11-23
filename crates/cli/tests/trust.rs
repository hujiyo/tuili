//! End-to-end tests for the official whitelist, trust labels and the
//! non-official dependency hint.
//!
//! Every case builds its own temporary `lawpacks` registry below its own
//! temporary root and runs the CLI with that root as its current directory, so
//! the tests do not depend on the repository's registry. The one exception is
//! the positive certificate case, which exercises the repository's official
//! `cn.constitution` registry from the repository root.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_lawpack::{build_lock, Lockfile, LOCK_FILE, OFFICIAL_FILE};

const PROVED: i32 = 0;
const LOAD_FAILED: i32 = 1;
const ERROR: i32 = 2;

const PACK: &str = "test.law";
const VERSION: &str = "0.1.0";
const CASE: &str = "case.std";
const GOAL: &str = "test.law.受处罚 张三";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn theory(namespace: &str) -> String {
    format!(
        r#"namespace {namespace}
sort {namespace}.人
pred {namespace}.违法 : {namespace}.人 → Prop
pred {namespace}.受处罚 : {namespace}.人 → Prop
rule {namespace}.违法即处罚 :
  params p : {namespace}.人
  premise {namespace}.违法 p
  conclude {namespace}.受处罚 p
  source text "测试" locator "一"
"#
    )
}

fn case_theory(imports: &[&str], namespace: &str) -> String {
    let mut text = String::new();
    for import in imports {
        text.push_str(&format!("import {import}\n"));
    }
    text.push_str(&format!(
        r#"obj 张三 : {namespace}.人
axiom 张三违法 : {namespace}.违法 张三
  source text "案件" locator "一"
"#
    ));
    text
}

fn manifest(name: &str, trust: &str) -> String {
    let mut text = format!(
        "[pack]\nname = \"{name}\"\nversion = \"{VERSION}\"\n\
         jurisdiction = \"CN\"\nterritory = \"CN\"\nnamespace = \"{name}\"\n\
         trust = \"{trust}\"\n"
    );
    if trust == "official" {
        text.push_str(
            "maintainers = [\"测试维护组\"]\n\
             audit_status = \"reviewed\"\n\
             audited_by = \"测试审核流程\"\n\
             audited_at = \"2026-11-23\"\n",
        );
    }
    text.push_str("\n[[files]]\npath = \"theory.std\"\nkind = \"theory\"\n");
    text
}

struct TempRoot {
    path: PathBuf,
}

impl TempRoot {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-trust-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("create {}: {error}", path.display()));
        TempRoot { path }
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

    /// Install one pack with a theory file.
    fn install(&self, name: &str, trust: &str) -> PathBuf {
        self.install_theory(name, trust, &theory(name))
    }

    /// Install one pack with an explicit theory source.
    fn install_theory(&self, name: &str, trust: &str, source: &str) -> PathBuf {
        let dir = self.lawpacks().join(name);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
        fs::write(dir.join("lawpack.toml"), manifest(name, trust))
            .unwrap_or_else(|error| panic!("write manifest: {error}"));
        fs::write(dir.join("theory.std"), source)
            .unwrap_or_else(|error| panic!("write theory: {error}"));
        dir
    }

    /// Hash every pack and write `<root>/lawpacks/std.lock`.
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

    fn lockfile(&self) -> Lockfile {
        Lockfile::read(&self.lawpacks().join(LOCK_FILE)).expect("the lock exists")
    }

    /// The hash and version the lock records for `name`.
    fn locked(&self, name: &str) -> (String, String) {
        let lockfile = self.lockfile();
        let entry = lockfile
            .pack
            .iter()
            .find(|entry| entry.name == name)
            .unwrap_or_else(|| panic!("no lock entry for `{name}`"));
        (entry.hash.clone(), entry.version.clone())
    }

    /// Write an `official.toml` from explicit `(name, version, hash)` entries.
    fn whitelist(&self, entries: &[(&str, &str, &str)]) {
        let mut text = String::new();
        for (name, version, hash) in entries {
            text.push_str(&format!(
                "[[pack]]\nname = \"{name}\"\nversion = \"{version}\"\nhash = \"{hash}\"\n\n"
            ));
        }
        self.write(&format!("lawpacks/{OFFICIAL_FILE}"), &text);
    }

    /// List every locked pack in `official.toml`.
    fn whitelist_all(&self) {
        let lockfile = self.lockfile();
        let mut text = String::new();
        for entry in &lockfile.pack {
            text.push_str(&format!(
                "[[pack]]\nname = \"{}\"\nversion = \"{}\"\nhash = \"{}\"\n\n",
                entry.name, entry.version, entry.hash
            ));
        }
        self.write(&format!("lawpacks/{OFFICIAL_FILE}"), &text);
    }

    fn run(&self, arguments: &[String]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_std-deduce"))
            .current_dir(&self.path)
            .args(arguments)
            .output()
            .unwrap_or_else(|error| panic!("failed to run the CLI: {error}"))
    }

    fn session(&self, options: &[&str], commands: &[String]) -> Output {
        let mut arguments: Vec<String> =
            options.iter().map(|option| (*option).to_owned()).collect();
        arguments.extend(commands.iter().cloned());
        self.run(&arguments)
    }
}

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn run_in(current_dir: &Path, arguments: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(current_dir)
        .args(arguments)
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

/// The certificate JSON a `:cert` run printed after its load report.
fn certificate_json(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    text[start..].trim_end().to_owned()
}

// ---------------------------------------------------------------------------
// The whitelist and `:packs`
// ---------------------------------------------------------------------------

/// The `:packs` first line of the pack whose name starts the line.
fn pack_line<'a>(out: &'a str, name: &str) -> &'a str {
    out.lines()
        .find(|line| line.starts_with(&format!("{name} ")))
        .unwrap_or_else(|| panic!("no listing line for `{name}`:\n{out}"))
}

#[test]
fn a_whitelisted_official_pack_passes_the_listing() {
    let root = TempRoot::new("listed");
    root.install(PACK, "official");
    root.lock();
    root.whitelist_all();

    let output = root.run(&[":packs lawpacks".to_owned()]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let line = pack_line(&out, PACK);
    assert!(
        line.contains("official（本项目审核）"),
        "a confirmed claim must read as audited:\n{line}"
    );
    for needle in [
        "  维护者：测试维护组",
        "  审核：已审核（审核人 测试审核流程，2026-11-23）",
        "  白名单：通过（official.toml）",
        "锁定校验：通过（1 个包）",
    ] {
        assert!(out.contains(needle), "missing {needle:?}:\n{out}");
    }
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn an_official_claim_without_a_whitelist_fails_the_listing() {
    let root = TempRoot::new("no-whitelist");
    root.install(PACK, "official");
    root.lock();

    let output = root.run(&[":packs lawpacks".to_owned()]);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let line = pack_line(&out, PACK);
    assert!(
        line.contains("official（未通过白名单核对）"),
        "an unconfirmed claim must not read as audited:\n{line}"
    );
    assert!(
        !line.contains("本项目审核"),
        "an unconfirmed claim must not borrow the audited label:\n{line}"
    );
    assert!(out.contains("没有官方白名单"), "{out}");
    assert!(out.contains(OFFICIAL_FILE), "{out}");
    assert!(
        !out.contains("白名单：通过"),
        "an unverified claim must not print a pass:\n{out}"
    );
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个官方白名单错误"]
    );
}

#[test]
fn a_whitelist_that_names_another_release_fails_the_listing() {
    let root = TempRoot::new("other-release");
    root.install(PACK, "official");
    root.lock();
    let (hash, version) = root.locked(PACK);
    let wrong_hash = {
        let last = if hash.ends_with('0') { '1' } else { '0' };
        format!("{}{last}", &hash[..hash.len() - 1])
    };

    for (tag, entry_version, entry_hash) in [
        ("version", "0.2.0", hash.as_str()),
        ("hash", version.as_str(), wrong_hash.as_str()),
    ] {
        root.whitelist(&[(PACK, entry_version, entry_hash)]);
        let output = root.run(&[":packs lawpacks".to_owned()]);
        assert_exit(&output, ERROR);
        let out = stdout(&output);
        let line = pack_line(&out, PACK);
        assert!(
            line.contains("official（未通过白名单核对）"),
            "{tag}: an unconfirmed claim must not read as audited:\n{line}"
        );
        assert!(!line.contains("本项目审核"), "{tag}: {line}");
        assert!(
            out.contains("未列入官方白名单，或锁哈希与白名单不一致"),
            "{tag}: {out}"
        );
        assert!(!out.contains("白名单：通过"), "{tag}: {out}");
        assert_eq!(
            stderr(&output).lines().collect::<Vec<_>>(),
            ["错误：1 个官方白名单错误"],
            "{tag}"
        );
    }
}

#[test]
fn a_community_pack_is_listed_without_a_whitelist() {
    let root = TempRoot::new("community");
    root.install(PACK, "community");
    root.lock();

    let output = root.run(&[":packs lawpacks".to_owned()]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    let line = pack_line(&out, PACK);
    assert!(
        line.contains("community（未经本项目审核）"),
        "a community pack keeps its own label:\n{line}"
    );
    assert!(!line.contains("official（"), "{line}");
    assert!(!out.contains("白名单"), "{out}");
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

#[test]
fn an_official_pack_without_a_lock_fails_the_listing() {
    let root = TempRoot::new("no-lock");
    root.install(PACK, "official");

    let output = root.run(&[":packs lawpacks".to_owned()]);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let line = pack_line(&out, PACK);
    assert!(
        line.contains("official（未通过白名单核对）"),
        "a claim without a lock hash must not read as audited:\n{line}"
    );
    assert!(!line.contains("本项目审核"), "{line}");
    assert!(out.contains("没有 std.lock"), "{out}");
    assert!(out.contains("锁定校验：未找到 std.lock（未锁定）"), "{out}");
    assert!(!out.contains("白名单：通过"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个官方白名单错误"]
    );
}

/// A failed lock check leaves no trustworthy hash, so even a listed release is
/// not rendered as audited.
#[test]
fn an_official_pack_with_a_changed_lock_fails_the_listing() {
    let root = TempRoot::new("lock-changed");
    root.install(PACK, "official");
    root.lock();
    root.whitelist_all();
    let theory = root.lawpacks().join(PACK).join("theory.std");
    let mut text = fs::read_to_string(&theory).expect("read the pack theory");
    text.push_str("\n-- 改动：破坏锁哈希\n");
    fs::write(&theory, text).expect("write the changed theory");

    let output = root.run(&[":packs lawpacks".to_owned()]);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let line = pack_line(&out, PACK);
    assert!(
        line.contains("official（未通过白名单核对）"),
        "a pack whose hash did not verify must not read as audited:\n{line}"
    );
    assert!(!line.contains("本项目审核"), "{line}");
    assert!(out.contains("哈希不符"), "{out}");
    assert!(!out.contains("白名单：通过"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个锁定校验错误"]
    );
}

/// Re-locking changed content leaves the whitelist naming the old hash, so the
/// release is no longer the audited one even though the lock itself verifies.
#[test]
fn a_relocked_pack_is_not_covered_by_the_stale_whitelist() {
    let root = TempRoot::new("relocked");
    root.install(PACK, "official");
    root.lock();
    root.whitelist_all();

    let theory = root.lawpacks().join(PACK).join("theory.std");
    let mut text = fs::read_to_string(&theory).expect("read the pack theory");
    text.push_str("\n-- 改动：重新锁定的内容\n");
    fs::write(&theory, text).expect("write the changed theory");
    root.lock();

    let output = root.run(&[":packs lawpacks".to_owned()]);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let line = pack_line(&out, PACK);
    assert!(
        line.contains("official（未通过白名单核对）"),
        "the relocked content is not the audited release:\n{line}"
    );
    assert!(!line.contains("本项目审核"), "{line}");
    assert!(
        out.contains("未列入官方白名单，或锁哈希与白名单不一致"),
        "{out}"
    );
    assert!(!out.contains("白名单：通过"), "{out}");
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个官方白名单错误"]
    );
}

/// A broken `official.toml` is a file-level error. It is printed once, with the
/// path escaped once (`path: error: ...`), and the official pack is not
/// rendered as audited.
#[test]
fn a_broken_whitelist_escapes_its_error_once() {
    let root = TempRoot::new("whitelist-broken");
    root.install(PACK, "official");
    root.lock();
    root.write(&format!("lawpacks/{OFFICIAL_FILE}"), "[[pack]\nname = \n");

    let output = root.run(&[":packs lawpacks".to_owned()]);
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let line = pack_line(&out, PACK);
    assert!(
        line.contains("official（未通过白名单核对）"),
        "a pack the whitelist cannot vouch for is not audited:\n{line}"
    );
    assert!(!line.contains("本项目审核"), "{line}");
    assert!(!out.contains("白名单：通过"), "{out}");

    assert_eq!(
        out.lines()
            .filter(|line| line.contains("官方白名单解析失败"))
            .count(),
        1,
        "the whitelist error is one line:\n{out}"
    );
    let error_line = out
        .lines()
        .find(|line| line.contains("官方白名单解析失败"))
        .unwrap_or_else(|| panic!("no whitelist error line:\n{out}"));
    assert!(
        error_line.contains("official.toml: error: "),
        "the error is rendered as `path: error: message`:\n{error_line}"
    );
    assert!(
        !error_line.contains(r"\\\\"),
        "the path must not be escaped twice:\n{error_line}"
    );
    assert!(
        !error_line.contains(r"\\n"),
        "the TOML message must not be escaped twice:\n{error_line}"
    );
    assert!(
        error_line.contains(r"\n"),
        "the TOML message's newline is escaped once:\n{error_line}"
    );
    assert_eq!(
        stderr(&output).lines().collect::<Vec<_>>(),
        ["错误：1 个官方白名单错误"]
    );
}

// ---------------------------------------------------------------------------
// The whitelist and imports
// ---------------------------------------------------------------------------

#[test]
fn an_official_pack_outside_the_whitelist_cannot_be_imported() {
    let root = TempRoot::new("import-unlisted");
    root.install(PACK, "official");
    root.lock();
    let case = root.write(CASE, &case_theory(&[PACK], PACK));
    let case_path = case.display().to_string();

    // No whitelist at all.
    let output = root.run(std::slice::from_ref(&case_path));
    assert_exit(&output, LOAD_FAILED);
    assert!(
        stderr(&output).contains("没有官方白名单"),
        "{}",
        stderr(&output)
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "a rejected import must not report a loaded theory:\n{}",
        stdout(&output)
    );

    // A whitelist that names another release.
    let (hash, _) = root.locked(PACK);
    root.whitelist(&[(PACK, "0.2.0", hash.as_str())]);
    let output = root.run(std::slice::from_ref(&case_path));
    assert_exit(&output, LOAD_FAILED);
    assert!(
        stderr(&output).contains("未列入官方白名单"),
        "{}",
        stderr(&output)
    );

    // The trust-gate option lowers only the profile requirement; it must not
    // accept an unverified `official` claim.
    let output = root.run(&["--allow-community-packs".to_owned(), case_path.clone()]);
    assert_exit(&output, LOAD_FAILED);
    assert!(
        stderr(&output).contains("白名单"),
        "--allow-community-packs must not bypass the whitelist:\n{}",
        stderr(&output)
    );

    // The same rejected import through the explicit `:load` command is a
    // command error (`2`), not a batch load failure (`1`).
    let output = root.run(&[format!(":load {case_path}")]);
    assert_exit(&output, ERROR);
    assert!(stderr(&output).contains("白名单"), "{}", stderr(&output));

    // The listed release with the locked hash imports normally.
    root.whitelist_all();
    let output = root.run(std::slice::from_ref(&case_path));
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(out.contains(&format!("已加载 `{case_path}`")), "{out}");
    assert!(out.contains(&format!("导入 {PACK}")), "{out}");
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
}

/// Dependencies are part of the environment closure, so an `official`
/// dependency the whitelist does not list fails the default environment and an
/// explicit import alike.
#[test]
fn an_unlisted_official_dependency_fails_the_environment_and_an_import() {
    let root = TempRoot::new("dependency-unlisted");
    root.install("pkg.b", "official");
    root.install_theory(
        "pkg.a",
        "official",
        &format!("import pkg.b\n{}", theory("pkg.a")),
    );
    root.write(
        "lawpacks/profiles/test.default.toml",
        "name = \"test.default\"\ndefault = true\ntrust = \"official\"\n\n\
         [[packs]]\nname = \"pkg.a\"\nversion = \"0.1\"\n",
    );
    root.lock();
    // Only the direct pack is listed; the dependency is not covered.
    let (hash, version) = root.locked("pkg.a");
    root.whitelist(&[("pkg.a", version.as_str(), hash.as_str())]);
    let case = root.write(CASE, &case_theory(&["pkg.a"], "pkg.a"));
    let case_path = case.display().to_string();

    // The default environment loads the profile's pack and then its dependency.
    let output = root.run(std::slice::from_ref(&case_path));
    assert_exit(&output, LOAD_FAILED);
    assert!(
        stderr(&output).contains("pkg.b") && stderr(&output).contains("白名单"),
        "the dependency must be named:\n{}",
        stderr(&output)
    );

    // An explicit import resolves the same closure.
    let output = root.run(&["--no-default-packs".to_owned(), case_path.clone()]);
    assert_exit(&output, LOAD_FAILED);
    assert!(
        stderr(&output).contains("pkg.b") && stderr(&output).contains("白名单"),
        "{}",
        stderr(&output)
    );
    assert!(
        !stdout(&output).contains("已加载"),
        "a rejected closure loads nothing:\n{}",
        stdout(&output)
    );

    // Covering the dependency as well makes the closure load.
    root.whitelist_all();
    let output = root.run(&[case_path]);
    assert_exit(&output, PROVED);
    assert!(stdout(&output).contains("已加载"), "{}", stdout(&output));
}

#[test]
fn a_whitelisted_official_pack_loads_as_the_default_environment() {
    let root = TempRoot::new("profile");
    root.install(PACK, "official");
    root.write(
        "lawpacks/profiles/test.default.toml",
        &format!(
            "name = \"test.default\"\naliases = [\"test\"]\ndefault = true\n\
             trust = \"official\"\n\n[[packs]]\nname = \"{PACK}\"\nversion = \"0.1\"\n"
        ),
    );
    root.lock();
    let case = root.write(CASE, &case_theory(&[], PACK));

    // Without the whitelist the default environment cannot honour the claim.
    let output = root.run(&[case.display().to_string()]);
    assert_exit(&output, LOAD_FAILED);
    assert!(stderr(&output).contains("白名单"), "{}", stderr(&output));

    root.whitelist_all();
    let output = root.run(&[case.display().to_string(), format!(":why {GOAL}")]);
    assert_exit(&output, PROVED);
    let out = stdout(&output);
    assert!(
        out.contains("默认环境 test.default：已加载 1 个包"),
        "{out}"
    );
    assert!(out.contains("推导已通过独立校验。"), "{out}");
}

// ---------------------------------------------------------------------------
// `:verify-cert`
// ---------------------------------------------------------------------------

#[test]
fn verify_cert_reports_every_non_official_pack() {
    let root = TempRoot::new("cert-community");
    root.install("pkg.community", "community");
    root.install("pkg.local", "local");
    root.lock();
    let goal = "pkg.community.受处罚 张三";
    let case = root.write(
        CASE,
        &case_theory(&["pkg.community", "pkg.local"], "pkg.community"),
    );
    let case_path = case.display().to_string();

    let generated = root.session(
        &[],
        &[format!(":load {case_path}"), format!(":cert {goal}")],
    );
    assert_exit(&generated, PROVED);
    let json = certificate_json(&generated);
    assert!(json.contains("\"trust\": \"community\""), "{json}");
    assert!(json.contains("\"trust\": \"local\""), "{json}");
    let certificate = root.write("certificate.json", &json);

    let checked = root.session(
        &[],
        &[
            format!(":load {case_path}"),
            format!(":verify-cert {}", certificate.display()),
        ],
    );
    assert_exit(&checked, PROVED);
    let out = stdout(&checked);
    assert!(
        out.contains("环境校验：通过（profile 未指定；包 2 个"),
        "{out}"
    );
    assert!(
        out.contains(
            "  注意：证书记录了非官方包：pkg.community@0.1.0（community）、pkg.local@0.1.0（local）；结论依赖这些包的定义"
        ),
        "{out}"
    );
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("内核证明：通过"), "{out}");
}

#[test]
fn verify_cert_does_not_flag_the_official_pack() {
    let example = repo_root().join("examples/宪法第三十九条-导入包.std");
    let goal = "cn.constitution.住宅受侵犯 张三 甲宅";

    let generated = run_in(
        &repo_root(),
        &[example.display().to_string(), format!(":cert {goal}")],
    );
    assert_exit(&generated, PROVED);
    let temp = TempRoot::new("cert-official");
    let certificate = temp.write("certificate.json", &certificate_json(&generated));

    let checked = run_in(
        &repo_root(),
        &[
            example.display().to_string(),
            format!(":verify-cert {}", certificate.display()),
        ],
    );
    assert_exit(&checked, PROVED);
    let out = stdout(&checked);
    assert!(out.contains("环境校验：通过（profile cn.default"), "{out}");
    assert!(
        !out.contains("非官方包"),
        "an official pack must get no trust warning:\n{out}"
    );
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(stderr(&checked).is_empty(), "{}", stderr(&checked));
}
