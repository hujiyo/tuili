//! End-to-end malformed-input tests through the real binary.
//!
//! The parser and certificate limits are unit-tested in their own crates; this
//! file checks that the CLI reports them as ordinary diagnostics with a
//! position and exit code `2`, and never dies with a stack overflow or a panic.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const LOAD_ERROR: i32 = 2;

fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
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

fn assert_load_error(output: &Output) {
    let code = output.status.code();
    assert_eq!(
        code,
        Some(LOAD_ERROR),
        "expected a load error ({LOAD_ERROR}), got {code:?}\nstdout:\n{}\nstderr:\n{}",
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
        let path = std::env::temp_dir().join(format!(
            "std-deduce-hardening-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
        TempDir { path }
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

fn load(path: &Path) -> Output {
    run(&[format!(":load {}", path.display())])
}

#[test]
fn an_empty_file_loads_with_no_declarations() {
    let dir = TempDir::new("empty");
    let path = dir.write("empty.std", "");
    let output = load(&path);
    let code = output.status.code();
    assert_eq!(
        code,
        Some(0),
        "an empty theory is valid\nstdout:\n{}\nstderr:\n{}",
        stdout(&output),
        stderr(&output)
    );
    assert!(
        stdout(&output).contains("已加载"),
        "the empty file must report a successful load, got:\n{}",
        stdout(&output)
    );
}

#[test]
fn invalid_utf8_is_a_read_error_not_a_panic() {
    let dir = TempDir::new("invalid-utf8");
    // A lone 0xFF byte is never valid UTF-8.
    let path = dir.write_bytes("invalid.std", &[0xFF, 0xFE, b'a', b'\n']);
    let output = load(&path);
    assert_load_error(&output);
    let err = stderr(&output);
    assert!(
        err.contains("读取失败"),
        "the error must say the file could not be read, got:\n{err}"
    );
    assert!(
        err.contains("invalid.std"),
        "the diagnostic must name the file, got:\n{err}"
    );
}

#[test]
fn a_control_character_reports_its_position() {
    let dir = TempDir::new("control");
    let path = dir.write("control.std", "sort 公\u{0}民\n");
    let output = load(&path);
    assert_load_error(&output);
    let err = stderr(&output);
    assert!(
        err.contains("无法识别的字符") && err.contains("\\u{0000}"),
        "the diagnostic must escape the control character, got:\n{err}"
    );
    assert!(
        err.contains(":1:7: error:"),
        "the diagnostic must carry the source position, got:\n{err}"
    );
}

#[test]
fn a_deeply_nested_term_is_a_parse_error_at_its_token() {
    let dir = TempDir::new("deep");
    let src = format!(
        "axiom 深 : {}Prop{}\n",
        "(".repeat(2_000),
        ")".repeat(2_000)
    );
    let path = dir.write("deep.std", &src);
    let output = load(&path);
    assert_load_error(&output);
    let err = stderr(&output);
    assert!(
        err.contains("嵌套深度超过上限"),
        "the error must name the depth limit, got:\n{err}"
    );
    assert!(
        err.contains(":1:"),
        "the error must be locatable, got:\n{err}"
    );
}

#[test]
fn an_overlong_identifier_is_a_lexical_error() {
    let dir = TempDir::new("long-ident");
    let path = dir.write("long.std", &format!("sort {}\n", "甲".repeat(2_000)));
    let output = load(&path);
    assert_load_error(&output);
    let err = stderr(&output);
    assert!(
        err.contains("标识符长度超过上限"),
        "the error must name the identifier limit, got:\n{err}"
    );
}

#[test]
fn a_rule_with_too_many_binders_is_refused() {
    let dir = TempDir::new("binders");
    let mut src = String::from("rule 长 :\n  params ");
    for index in 0..70 {
        if index > 0 {
            src.push_str(", ");
        }
        src.push_str(&format!("x{index} : 公民"));
    }
    src.push_str("\n  conclude 结论\n");
    let path = dir.write("binders.std", &src);
    let output = load(&path);
    assert_load_error(&output);
    let err = stderr(&output);
    assert!(
        err.contains("参数与前提合计超过上限"),
        "the error must name the telescope limit, got:\n{err}"
    );
}

#[test]
fn a_deeply_nested_certificate_is_rejected_before_checking() {
    let dir = TempDir::new("cert");
    let theory = dir.write(
        "theory.std",
        "sort 公民\npred 好人 : 公民 → Prop\nobj 张三 : 公民\n\
         axiom 张三是好人 : 好人 张三\n  source text \"测试\" locator \"夹具\"\n",
    );
    let depth = 5_000;
    let expression = format!(
        "{}{}{}",
        "{\"kind\":\"app\",\"func\":".repeat(depth),
        "{\"kind\":\"const\",\"name\":\"p\"}",
        ",\"arg\":{\"kind\":\"const\",\"name\":\"x\"}}".repeat(depth)
    );
    let certificate = format!(
        "{{\"format_version\":5,\"environment\":{{\"profile\":null,\"packs\":[],\
         \"corpora\":[],\"as_of\":null,\"jurisdiction\":null}},\"assumptions\":[],\
         \"nodes\":[{{\"kind\":\"gap\",\"proposition\":{expression}}}],\"root\":null,\
         \"conflicts\":[],\"open_obligations\":[],\"metadata\":{{}}}}"
    );
    let path = dir.write("deep.json", &certificate);
    let output = run(&[
        format!(":load {}", theory.display()),
        format!(":verify-cert {}", path.display()),
    ]);
    let code = output.status.code();
    assert_eq!(
        code,
        Some(LOAD_ERROR),
        "a malformed certificate must exit with {LOAD_ERROR}\nstdout:\n{}\nstderr:\n{}",
        stdout(&output),
        stderr(&output)
    );
    let err = stderr(&output);
    assert!(
        err.contains("不是有效的证书 JSON"),
        "the error must name the invalid certificate JSON, got:\n{err}"
    );
    assert!(
        !err.contains("panicked"),
        "a malformed certificate must not panic:\n{err}"
    );
}
