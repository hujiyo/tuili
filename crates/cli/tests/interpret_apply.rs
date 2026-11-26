//! End-to-end tests for enabling `interpret` declarations and for the v11
//! certificate that records an interpretation application.
//!
//! The default session must stay byte-for-byte identical: an interpretation is
//! enabled only by `--interpret` or `:interpret enable`, and the tests below
//! check both the unenabled hint and the enabled proof.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP: i32 = 1;
const COMMAND_ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
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

fn check_stdout(output: Output, expected: i32, needles: &[&str]) -> Output {
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

fn certificate_value(output: &Output) -> serde_json::Value {
    serde_json::from_str(&certificate_json(output)).expect("the printed certificate is valid JSON")
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-interpret-apply-{}-{tag}-{n}",
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

/// `P 张三` is registered, `解释` would turn it into `Q 张三`.
const CASE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
obj 张三 : 人
axiom 事实 : P 张三
  source text "案情" locator "一"
interpret 解释 : P 张三 → Q 张三
  direction literal
  source text "解释文本" locator "一" version "2020"
"#;

fn case_file(tag: &str) -> (TempDir, PathBuf) {
    let temp = TempDir::new(tag);
    let case = temp.write("case.std", CASE);
    (temp, case)
}

#[test]
fn an_unenabled_interpretation_shows_up_as_a_gap_with_a_hint() {
    let (_temp, case) = case_file("hint");
    let path = case.display().to_string();
    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":gap Q 张三".to_owned(),
        ]),
        GAP,
        &[
            "无法推出 Q 张三",
            "存在未启用解释 `解释`（P 张三 → Q 张三）；用 :interpret enable 解释 后重查",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("由解释推出"),
        "an unenabled interpretation must not be applied:\n{out}"
    );

    // `:why` reports the same gap and the same hint.
    let (_temp, case) = case_file("hint-why");
    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            case.display().to_string(),
            ":why Q 张三".to_owned(),
        ]),
        GAP,
        &[
            "根为缺口",
            "存在未启用解释 `解释`（P 张三 → Q 张三）；用 :interpret enable 解释 后重查",
        ],
    );
    assert!(
        !stdout(&output).contains("推导已通过独立校验。"),
        "a gap must not be reported as a proof:\n{}",
        stdout(&output)
    );
}

#[test]
fn the_flag_enables_the_interpretation_step() {
    let (_temp, case) = case_file("flag");
    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "解释".to_owned(),
            case.display().to_string(),
            ":why Q 张三".to_owned(),
        ]),
        PROVED,
        &["推导已通过独立校验。", "〈解释 解释（literal）〉"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("存在未启用解释"),
        "the enabled interpretation must not be offered as a hint:\n{out}"
    );

    // The narrative renders the same step as a because-so sentence instead of
    // a rule application.
    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "解释".to_owned(),
            case.display().to_string(),
            ":explain Q 张三".to_owned(),
        ]),
        PROVED,
        &[
            "【结论】「Q 张三」由解释推出。",
            "根据解释「解释」（方向 literal），所以「Q 张三」成立。",
            "推导已通过独立校验。",
        ],
    );
    assert!(
        !stdout(&output).contains("根据规则"),
        "an interpretation step must not be narrated as a rule:\n{}",
        stdout(&output)
    );
}

#[test]
fn the_session_command_enables_and_disables_the_interpretation() {
    let (_temp, case) = case_file("command");
    let path = case.display().to_string();

    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":interpret list".to_owned(),
            ":interpret enable 解释".to_owned(),
            ":interpret list".to_owned(),
            ":why Q 张三".to_owned(),
        ]),
        PROVED,
        &[
            "[未启用] 解释 : P 张三 → Q 张三 〔方向 literal〕",
            "已启用解释 `解释`（P 张三 → Q 张三）。",
            "[已启用] 解释 : P 张三 → Q 张三 〔方向 literal〕",
            "推导已通过独立校验。",
        ],
    );
    let out = stdout(&output);
    assert!(
        out.matches("[已启用] 解释").count() == 1,
        "exactly the second :interpret list line must be enabled:\n{out}"
    );

    // A later command in the same session disables it again; the query is a
    // gap and the hint comes back.
    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":interpret enable 解释".to_owned(),
            ":interpret disable 解释".to_owned(),
            ":why Q 张三".to_owned(),
        ]),
        GAP,
        &["已停用解释 `解释`。", "根为缺口"],
    );
    let out = stdout(&output);
    assert!(
        out.contains("存在未启用解释 `解释`"),
        "the disabled interpretation must be hinted again:\n{out}"
    );
}

#[test]
fn enabling_an_unknown_or_duplicate_or_equivalent_interpretation_is_an_error() {
    let (_temp, case) = case_file("invalid");
    let path = case.display().to_string();

    check_stderr(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":interpret enable 不存在".to_owned(),
        ]),
        COMMAND_ERROR,
        &["不存在"],
    );

    check_stderr(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":interpret enable 解释".to_owned(),
            ":interpret enable 解释".to_owned(),
        ]),
        COMMAND_ERROR,
        &["已经启用"],
    );

    // Two interpretations whose `to` are kernel-equivalent may not be enabled
    // together: the conclusion would not be auditable.
    let temp = TempDir::new("equivalent");
    let case = temp.write(
        "case.std",
        "sort 人\npred P : 人 → Prop\npred R : 人 → Prop\npred Q : 人 → Prop\n\
         obj 张三 : 人\n\
         axiom 事实P : P 张三\n  source text \"案情\" locator \"一\"\n\
         axiom 事实R : R 张三\n  source text \"案情\" locator \"二\"\n\
         interpret i1 : P 张三 → Q 张三\n  direction literal\n\
         \x20 source text \"解释\" locator \"一\" version \"2020\"\n\
         interpret i2 : R 张三 → Q 张三\n  direction expand\n\
         \x20 source text \"解释\" locator \"二\" version \"2020\"\n",
    );
    let output = check_stderr(
        run(&[
            "--no-default-packs".to_owned(),
            case.display().to_string(),
            ":interpret enable i1".to_owned(),
            ":interpret enable i2".to_owned(),
        ]),
        COMMAND_ERROR,
        &["核下等价", "i1", "disable"],
    );
    assert!(
        !stdout(&output).contains("已启用解释 `i2`"),
        "the rejected interpretation must not be enabled:\n{}",
        stdout(&output)
    );

    // The same invalid setting on the command line fails the load it is used
    // with, before any query runs.
    check_stderr(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "不存在".to_owned(),
            path,
        ]),
        GAP,
        &["不存在"],
    );
}

#[test]
fn two_enabled_interpretations_are_listed_by_id_in_the_certificate() {
    let temp = TempDir::new("two");
    let case = temp.write(
        "case.std",
        "sort 人\npred P : 人 → Prop\npred R : 人 → Prop\n\
         pred Q : 人 → Prop\npred S : 人 → Prop\nobj 张三 : 人\n\
         axiom 事实P : P 张三\n  source text \"案情\" locator \"一\"\n\
         axiom 事实R : R 张三\n  source text \"案情\" locator \"二\"\n\
         interpret iB : P 张三 → Q 张三\n  direction literal\n\
         \x20 source text \"解释\" locator \"一\" version \"2020\"\n\
         interpret iA : R 张三 → S 张三\n  direction analogy\n\
         \x20 source text \"解释\" locator \"二\" version \"2020\"\n",
    );
    let path = case.display().to_string();

    // The order of --interpret flags must not change the certificate: the
    // interpretations table is sorted by id and the nodes by conclusion.
    let first = run(&[
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "iB".to_owned(),
        "--interpret".to_owned(),
        "iA".to_owned(),
        path.clone(),
        ":cert Q 张三".to_owned(),
    ]);
    assert_exit(&first, PROVED);
    let second = run(&[
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "iA".to_owned(),
        "--interpret".to_owned(),
        "iB".to_owned(),
        path,
        ":cert Q 张三".to_owned(),
    ]);
    assert_exit(&second, PROVED);
    assert_eq!(
        certificate_json(&first),
        certificate_json(&second),
        "certificate output depends on the order interpretations were enabled"
    );

    let value = certificate_value(&first);
    assert_eq!(value["format_version"], 11);
    let interpretations = value["interpretations"]
        .as_array()
        .expect("v11 records an interpretations array");
    assert_eq!(interpretations.len(), 2);
    assert_eq!(interpretations[0]["id"], "iA");
    assert_eq!(interpretations[1]["id"], "iB");
    assert_eq!(interpretations[1]["direction"], "literal");

    // Both applications are nodes, and each refers to the interpretations
    // table by index.
    let nodes = value["nodes"].as_array().unwrap();
    let applications: Vec<&serde_json::Value> = nodes
        .iter()
        .filter(|node| node["kind"] == "interpretation_application")
        .collect();
    assert_eq!(applications.len(), 2, "{value:#}");
    for application in applications {
        let index = application["interpretation"].as_u64().unwrap() as usize;
        assert_eq!(
            interpretations[index]["to"], application["conclusion"],
            "the node index must select the interpretation that concludes it"
        );
        let premise = application["premise"].as_u64().unwrap() as usize;
        assert_eq!(nodes[premise]["kind"], "assumption", "{value:#}");
    }
}

#[test]
fn the_certificate_records_the_interpretation_and_its_application() {
    let (_temp, case) = case_file("cert");
    let output = run(&[
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "解释".to_owned(),
        case.display().to_string(),
        ":cert Q 张三".to_owned(),
    ]);
    assert_exit(&output, PROVED);
    let value = certificate_value(&output);
    assert_eq!(value["format_version"], 11);
    let interpretations = value["interpretations"].as_array().unwrap();
    assert_eq!(interpretations.len(), 1);
    assert_eq!(interpretations[0]["id"], "解释");
    assert_eq!(interpretations[0]["direction"], "literal");
    assert_eq!(interpretations[0]["from"]["kind"], "app");
    assert_eq!(interpretations[0]["to"]["kind"], "app");
    assert_eq!(
        interpretations[0]["sources"][0]["text"], "解释文本",
        "the interpretation's provenance must be recorded"
    );

    let root = value["root"].as_u64().unwrap() as usize;
    assert_eq!(
        value["nodes"][root]["kind"], "interpretation_application",
        "the root is the interpretation's application step"
    );
    assert_eq!(value["nodes"][root]["interpretation"], 0);
    assert_eq!(value["nodes"][root]["premise"], 0);
}

#[test]
fn a_v5_certificate_is_rejected_with_the_version_probe() {
    let (_temp, case) = case_file("v5");
    let output = run(&[
        "--no-default-packs".to_owned(),
        case.display().to_string(),
        ":cert Q 张三".to_owned(),
    ]);
    // The gap certificate is still a certificate; generate one that is valid
    // enough to be written, then downgrade its version field.
    assert_exit(&output, GAP);
    let mut value = certificate_value(&output);
    value["format_version"] = serde_json::Value::from(5);
    let cert_path = _temp.write("cert.json", &serde_json::to_string_pretty(&value).unwrap());
    let output = check_stderr(
        run(&[
            "--no-default-packs".to_owned(),
            case.display().to_string(),
            format!(":verify-cert {}", cert_path.display()),
        ]),
        COMMAND_ERROR,
        &[
            "unsupported certificate format version 5",
            "this build supports 11",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("逻辑校验：通过"),
        "the version probe must run before either proof layer:\n{out}"
    );
}

/// A case with a rule that concludes `R 张三`, declared contrary to `Q 张三`.
/// The interpretation derives `Q 张三`, so the conflict witness is the
/// interpretation itself.
const CONFLICT_CASE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
obj 张三 : 人
contrary Q R
axiom 事实 : P 张三
  source text "案情" locator "一"
rule 规则R :
  conclude R 张三
  source text "规则文本" locator "一"
interpret 解释 : P 张三 → Q 张三
  direction literal
  source text "解释文本" locator "一" version "2020"
"#;

#[test]
fn a_conflict_witness_can_be_an_interpretation() {
    let temp = TempDir::new("conflict");
    let case = temp.write("case.std", CONFLICT_CASE);
    let path = case.display().to_string();

    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "解释".to_owned(),
            path.clone(),
            ":why Q 张三".to_owned(),
        ]),
        GAP,
        &["冲突未决", "解释⟨解释⟩"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("已无可重建的规则实例"),
        "an interpretation witness must not be reported as a lost rule witness:\n{out}"
    );

    let output = run(&[
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "解释".to_owned(),
        path,
        ":cert Q 张三".to_owned(),
    ]);
    assert_exit(&output, GAP);
    let value = certificate_value(&output);
    let provenance = &value["conflicts"][0]["right_by"];
    let provenance = if provenance["kind"] == "interpretation" {
        provenance
    } else {
        &value["conflicts"][0]["left_by"]
    };
    assert_eq!(
        provenance["kind"], "interpretation",
        "the conflict witness must be recorded as an interpretation: {value:#}"
    );
    let index = provenance["interpretation"].as_u64().unwrap() as usize;
    assert_eq!(value["interpretations"][index]["id"], "解释");
    assert!(
        value["open_obligations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|obligation| obligation["kind"] == "unresolved_conflict"),
        "the unresolved interpretation conflict must stay an open obligation: {value:#}"
    );
}

/// Generate a valid v11 certificate for `Q 张三` and then hand-edit it.
fn forged_certificate(
    edit: impl FnOnce(&mut serde_json::Value),
    tag: &str,
) -> (TempDir, PathBuf, PathBuf) {
    let temp = TempDir::new(tag);
    let case = temp.write("case.std", CASE);
    let output = run(&[
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "解释".to_owned(),
        case.display().to_string(),
        ":cert Q 张三".to_owned(),
    ]);
    assert_exit(&output, PROVED);
    let mut value = certificate_value(&output);
    edit(&mut value);
    let cert = temp.write("cert.json", &serde_json::to_string_pretty(&value).unwrap());
    (temp, case, cert)
}

fn verify(case: &Path, cert: &Path) -> Output {
    run(&[
        "--no-default-packs".to_owned(),
        case.display().to_string(),
        format!(":verify-cert {}", cert.display()),
    ])
}

#[test]
fn a_forged_interpretation_application_is_rejected() {
    // 1. Out-of-range interpretation index.
    let (temp, case, cert) = forged_certificate(
        |value| {
            let root = value["root"].as_u64().unwrap() as usize;
            value["nodes"][root]["interpretation"] = serde_json::Value::from(7);
        },
        "bad-index",
    );
    check_stderr(verify(&case, &cert), COMMAND_ERROR, &["解释", "7"]);
    drop(temp);

    // 2. The table is emptied while the application node still cites entry 0.
    // The rejection must name the missing entry, not fail for some unrelated
    // reason that merely happens to mention interpretations.
    let (temp, case, cert) = forged_certificate(
        |value| value["interpretations"] = serde_json::Value::Array(Vec::new()),
        "unlisted",
    );
    check_stderr(
        verify(&case, &cert),
        COMMAND_ERROR,
        &[
            "解释应用或冲突见证引用了不存在的解释 0：证书只有 0 条解释",
            "证书校验失败（逻辑层）",
        ],
    );
    drop(temp);

    // 3. The `from` does not match the environment declaration.
    let (temp, case, cert) = forged_certificate(
        |value| {
            value["interpretations"][0]["from"] = serde_json::json!({"kind": "app", "func": {"kind": "const", "name": "Q"},
                                   "arg": {"kind": "const", "name": "张三"}});
        },
        "bad-from",
    );
    check_stderr(verify(&case, &cert), COMMAND_ERROR, &["的 from 是"]);
    drop(temp);

    // 4. The `to` does not match the environment declaration, even when the
    // node and the entry agree with each other.
    let (temp, case, cert) = forged_certificate(
        |value| {
            let replaced = serde_json::json!({"kind": "app",
                "func": {"kind": "const", "name": "P"},
                "arg": {"kind": "const", "name": "张三"}});
            value["interpretations"][0]["to"] = replaced.clone();
            let root = value["root"].as_u64().unwrap() as usize;
            value["nodes"][root]["conclusion"] = replaced;
        },
        "bad-to",
    );
    check_stderr(verify(&case, &cert), COMMAND_ERROR, &["的 to 是"]);
    drop(temp);

    // 5. The conclusion is not the interpretation's `to`.
    let (temp, case, cert) = forged_certificate(
        |value| {
            let root = value["root"].as_u64().unwrap() as usize;
            value["nodes"][root]["conclusion"] = serde_json::json!({"kind": "app",
                "func": {"kind": "const", "name": "P"},
                "arg": {"kind": "const", "name": "张三"}});
        },
        "bad-conclusion",
    );
    check_stderr(verify(&case, &cert), COMMAND_ERROR, &["结论"]);
    drop(temp);

    // 6. The premise is not the interpretation's `from`: point it at a later
    // node (the application itself).
    let (temp, case, cert) = forged_certificate(
        |value| {
            let root = value["root"].as_u64().unwrap() as usize;
            value["nodes"][root]["premise"] = serde_json::Value::from(root as u64);
        },
        "bad-premise",
    );
    check_stderr(verify(&case, &cert), COMMAND_ERROR, &["前提"]);
    drop(temp);
}

#[test]
fn an_interpretation_that_the_environment_does_not_declare_is_rejected() {
    let (temp, case, cert) = forged_certificate(
        |value| value["interpretations"][0]["id"] = serde_json::Value::from("不存在"),
        "missing-declaration",
    );
    check_stderr(verify(&case, &cert), COMMAND_ERROR, &["解释", "不存在"]);
    drop(temp);
}

#[test]
fn the_interpretations_field_is_mandatory() {
    let (temp, case, cert) = forged_certificate(
        |value| {
            value
                .as_object_mut()
                .unwrap()
                .remove("interpretations")
                .expect("the certificate has interpretations");
        },
        "missing-field",
    );
    check_stderr(
        verify(&case, &cert),
        COMMAND_ERROR,
        &["missing field `interpretations`"],
    );
    drop(temp);
}

/// `Q` is only an interpretation conclusion; the rule needs `Q` and `Z`.
const RULE_GAP_CASE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred Z : 人 → Prop
pred S : 人 → Prop
obj 张三 : 人
axiom 事实 : P 张三
  source text "案情" locator "一"
interpret 解释 : P 张三 → Q 张三
  direction literal
  source text "解释文本" locator "一" version "2020"
rule 规则S :
  premise Q 张三
  premise Z 张三
  conclude S 张三
  source text "规则文本" locator "一"
"#;

#[test]
fn gap_diagnostics_do_not_count_interpretation_conclusions_as_rule_premises() {
    let temp = TempDir::new("rule-gap");
    let case = temp.write("case.std", RULE_GAP_CASE);
    let path = case.display().to_string();

    // Without enabling, `Q` is missing too, and the hint is not offered for a
    // rule premise: enabling the interpretation cannot make the rule fire.
    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            path.clone(),
            ":gap S 张三".to_owned(),
        ]),
        GAP,
        &["缺 ⟨Q 张三⟩", "缺 ⟨Z 张三⟩"],
    );
    assert!(
        !stdout(&output).contains("存在未启用解释"),
        "a rule premise is not an interpretation hint:\n{}",
        stdout(&output)
    );

    // `:why` reads the same candidate list from the certificate: `Q` stays
    // missing even though an enabled interpretation licenses it.
    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "解释".to_owned(),
            path.clone(),
            ":why S 张三".to_owned(),
        ]),
        GAP,
        &["缺：Q 张三；Z 张三"],
    );
    assert!(
        !stdout(&output).contains("存在未启用解释"),
        "the enabled interpretation is not a hint:\n{}",
        stdout(&output)
    );

    // `:issues` expands the same gap tree and must not call `Q` satisfied.
    check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "解释".to_owned(),
            path.clone(),
            ":issues".to_owned(),
        ]),
        GAP,
        &[
            "争点 ⟨S 张三⟩",
            "缺 ⟨Q 张三⟩",
            "缺 ⟨Z 张三⟩",
            "该命题已由解释推出，但规则阶段不消费解释结论",
        ],
    );

    // The certificate's gap candidate records both missing premises.
    let output = run(&[
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "解释".to_owned(),
        path,
        ":cert S 张三".to_owned(),
    ]);
    assert_exit(&output, GAP);
    let value = certificate_value(&output);
    let root = value["root"].as_u64().expect("the gap root is recorded") as usize;
    assert_eq!(value["nodes"][root]["kind"], "gap");
    let missing = value["nodes"][root]["candidates"][0]["missing"]
        .as_array()
        .expect("the candidate records its missing premises");
    assert_eq!(missing.len(), 2, "{value:#}");
    let names: Vec<&str> = missing
        .iter()
        .map(|premise| {
            premise["func"]["name"]
                .as_str()
                .expect("a missing premise is an application")
        })
        .collect();
    assert_eq!(names, ["Q", "Z"], "{value:#}");
}

/// `i1 : P → Q` and `i2 : Q → R`: enabling `i2` would consume `i1`'s
/// conclusion, which this build never does.
const CHAIN_CASE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
obj 张三 : 人
axiom 事实 : P 张三
  source text "案情" locator "一"
interpret i1 : P 张三 → Q 张三
  direction literal
  source text "解释文本" locator "一" version "2020"
interpret i2 : Q 张三 → R 张三
  direction analogy
  source text "解释文本二" locator "二" version "2020"
"#;

#[test]
fn a_hint_is_not_offered_when_enabling_would_chain() {
    let temp = TempDir::new("hint-chain");
    let case = temp.write("case.std", CHAIN_CASE);
    let path = case.display().to_string();

    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "i1".to_owned(),
            path.clone(),
            ":gap R 张三".to_owned(),
        ]),
        GAP,
        &["无法推出 R 张三"],
    );
    assert!(
        !stdout(&output).contains("存在未启用解释"),
        "`i2` reads `i1`'s conclusion, so enabling it is a dead end:\n{}",
        stdout(&output)
    );

    // With nothing enabled, the direct root hint for `Q` is still printed.
    check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            path,
            ":gap Q 张三".to_owned(),
        ]),
        GAP,
        &["存在未启用解释 `i1`"],
    );
}

#[test]
fn a_chained_certificate_is_rejected_by_verify_cert() {
    let temp = TempDir::new("chain-cert");
    let case = temp.write("case.std", CHAIN_CASE);
    let output = run(&[
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "i1".to_owned(),
        case.display().to_string(),
        ":cert Q 张三".to_owned(),
    ]);
    assert_exit(&output, PROVED);
    let mut value = certificate_value(&output);
    // Append `i2` and an application that reads node 1 (`Q`, licensed by
    // `i1`). Every step typechecks on its own; only the "no interpretation
    // chain" invariant rejects the graph.
    value["interpretations"]
        .as_array_mut()
        .expect("the v11 table is an array")
        .push(serde_json::json!({
            "id": "i2",
            "direction": "analogy",
            "from": {"kind": "app", "func": {"kind": "const", "name": "Q"},
                     "arg": {"kind": "const", "name": "张三"}},
            "to": {"kind": "app", "func": {"kind": "const", "name": "R"},
                   "arg": {"kind": "const", "name": "张三"}},
            "sources": [{"text": "解释文本二", "locator": "二", "version": "2020"}]
        }));
    value["nodes"]
        .as_array_mut()
        .expect("the node list is an array")
        .push(serde_json::json!({
            "kind": "interpretation_application",
            "interpretation": 1,
            "premise": 1,
            "conclusion": {"kind": "app", "func": {"kind": "const", "name": "R"},
                           "arg": {"kind": "const", "name": "张三"}}
        }));
    value["root"] = serde_json::Value::from(2);
    let cert = temp.write("cert.json", &serde_json::to_string_pretty(&value).unwrap());
    check_stderr(
        verify(&case, &cert),
        COMMAND_ERROR,
        &["禁止解释链", "证书校验失败（逻辑层）"],
    );
}

/// A non-strict claim against an interpretation conclusion.
const CLAIM_CASE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
obj 张三 : 人
contrary Q R
axiom 事实P : P 张三
  source text "案情" locator "一"
axiom 主张R : R 张三
  source text "案情" locator "二"
interpret 解释 : P 张三 → Q 张三
  direction literal
  source text "解释文本" locator "一" version "2020"
"#;

#[test]
fn a_non_strict_claim_against_an_interpretation_says_so() {
    let temp = TempDir::new("claim-vs-interpretation");
    let case = temp.write("case.std", CLAIM_CASE);
    let path = case.display().to_string();

    let output = check_stdout(
        run(&[
            "--no-default-packs".to_owned(),
            "--interpret".to_owned(),
            "解释".to_owned(),
            path.clone(),
            ":why Q 张三".to_owned(),
        ]),
        GAP,
        &["未经证明，不能自动胜过解释结论"],
    );
    assert!(
        !stdout(&output).contains("不能自动胜过规则结论"),
        "an interpretation is not a rule:\n{}",
        stdout(&output)
    );

    // The certificate's unresolved-conflict description uses the same wording.
    let output = run(&[
        "--no-default-packs".to_owned(),
        "--interpret".to_owned(),
        "解释".to_owned(),
        path,
        ":cert Q 张三".to_owned(),
    ]);
    assert_exit(&output, GAP);
    let value = certificate_value(&output);
    let description = value["open_obligations"]
        .as_array()
        .expect("the certificate records open obligations")
        .iter()
        .find(|obligation| obligation["id"] == "conflict-0")
        .and_then(|obligation| obligation["description"].as_str())
        .expect("the unresolved conflict has a description");
    assert!(
        description.contains("不能自动胜过解释结论"),
        "{description}"
    );
}
