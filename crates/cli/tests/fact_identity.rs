//! End-to-end tests for fact identity in `:why`, `:cert` and `:verify-cert`.
//!
//! Each test drives the real binary: a theory file is loaded, the query output
//! is asserted, and where a certificate is involved it is parsed as JSON and
//! checked by a second process that only loads the theory and runs
//! `:verify-cert`. The assertions pin exit codes and stable substrings, not
//! whole-output snapshots.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_cert::{Certificate, FactIdentity};

const PROVED: i32 = 0;
const GAP_OR_CONFLICT: i32 = 1;
const ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Run the CLI from the repository root: the default environment resolves
/// `lawpacks/` relative to the working directory.
fn run(commands: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(commands)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

/// A temporary file removed when the test ends (including on panic).
struct TempFile {
    path: PathBuf,
}

impl TempFile {
    fn new(tag: &str, suffix: &str, contents: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-fact-identity-{}-{tag}-{n}.{suffix}",
            std::process::id()
        ));
        fs::write(&path, contents).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempFile { path }
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn session(theory: &TempFile, commands: &[&str]) -> Output {
    let mut all = vec![format!(":load {}", theory.path.display())];
    all.extend(commands.iter().map(|command| command.to_string()));
    run(all)
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

/// Assert the exit code and that stderr contains every needle.
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

/// `:cert` prints its JSON after the load report, so the certificate is the
/// tail starting at the first `{`.
fn certificate_json(output: &Output) -> Certificate {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    Certificate::from_json(text[start..].trim_end())
        .unwrap_or_else(|error| panic!("invalid certificate JSON:\n{error}\nstdout:\n{text}"))
}

fn verify_cert(theory: &TempFile, tag: &str, certificate: &Certificate) -> Output {
    let json = certificate.to_json_pretty().unwrap();
    let file = TempFile::new(tag, "json", &json);
    session(theory, &[&format!(":verify-cert {}", file.path.display())])
}

/// The assumption a certificate records for `proposition`.
fn assumption_identity(certificate: &Certificate, proposition: &str) -> FactIdentity {
    certificate
        .assumptions
        .iter()
        .find(|assumption| {
            std_deduce_kernel::pretty::print_expr(&std_deduce_kernel::Expr::from(
                &assumption.proposition,
            )) == proposition
        })
        .unwrap_or_else(|| {
            panic!(
                "the certificate records no assumption `{proposition}`: {:?}",
                certificate.assumptions
            )
        })
        .identity
}

/// A rule that concludes one side of a declared contradiction.
fn contradiction_theory(fact: &str) -> String {
    format!(
        r#"
sort 申请
pred 符合条件 : 申请 → Prop
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
contrary 批准 不批准
obj 甲 : 申请
axiom 条件 : 符合条件 甲
  source text "申请人" locator "材料"
{fact}
rule 拒绝 :
  params x : 申请
  premise 符合条件 x
  conclude 不批准 x
  source text "许可法" locator "第三十九条"
"#
    )
}

/// A strict fact outranks a defeasible rule conclusion. The query for the
/// winner succeeds, states the basis, and the exported certificate records the
/// fact's identity. The query for the loser is a defeat, and its winning-side
/// description carries the same identity.
#[test]
fn strict_fact_defeats_a_rule_conclusion() {
    let theory = TempFile::new(
        "strict-vs-rule",
        "std",
        &contradiction_theory(
            r#"axiom 已批准 : 批准 甲
  identity verified
  source text "判决" locator "第一页""#,
        ),
    );

    check(
        session(&theory, &[":why 批准 甲"]),
        PROVED,
        &[
            "冲突（已裁决）",
            "依据：严格事实优先于可废止规则结论。",
            "推导已通过独立校验",
        ],
    );
    check(
        session(&theory, &[":why 不批准 甲"]),
        GAP_OR_CONFLICT,
        &[
            "冲突已裁决：",
            "事实〔法院查明〕",
            "依据：严格事实优先于可废止规则结论。",
        ],
    );

    let certificate = check(session(&theory, &[":cert 批准 甲"]), PROVED, &[]);
    let certificate = certificate_json(&certificate);
    assert_eq!(
        assumption_identity(&certificate, "批准 甲"),
        FactIdentity::Verified
    );
    let checked = verify_cert(&theory, "strict-vs-rule", &certificate);
    // The root is the assumption, so the summary names the identity it was
    // registered under.
    check(checked, PROVED, &["逻辑校验：通过", "根为假设（法院查明）"]);
}

/// A strict fact also outranks another fact that is merely a claim. The basis
/// sentence names the claim, not a rule conclusion.
#[test]
fn strict_fact_defeats_a_claim() {
    let theory = TempFile::new(
        "strict-vs-claim",
        "std",
        r#"
sort 申请
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
contrary 批准 不批准
obj 甲 : 申请
axiom 已批准 : 批准 甲
  identity verified
  source text "判决" locator "第一页"
axiom 未批准 : 不批准 甲
  identity user_asserted
  source text "当事人主张" locator "答辩状"
"#,
    );

    check(
        session(&theory, &[":why 批准 甲"]),
        PROVED,
        &["冲突（已裁决）", "依据：严格事实优先于未经证明的主张。"],
    );
    check(
        session(&theory, &[":why 不批准 甲"]),
        GAP_OR_CONFLICT,
        &["事实〔法院查明〕", "依据：严格事实优先于未经证明的主张。"],
    );

    let certificate = check(session(&theory, &[":cert 批准 甲"]), PROVED, &[]);
    let certificate = certificate_json(&certificate);
    assert_eq!(
        assumption_identity(&certificate, "批准 甲"),
        FactIdentity::Verified
    );
    assert_eq!(
        assumption_identity(&certificate, "不批准 甲"),
        FactIdentity::UserAsserted
    );
}

/// A claim never automatically beats a rule conclusion: the conflict stays
/// unresolved, `:why` names the claim and its identity, the certificate records
/// `non_strict_fact` with the claim's identity, and `:verify-cert` exits `1`.
#[test]
fn claim_against_a_rule_stays_unresolved() {
    let theory = TempFile::new(
        "claim-vs-rule",
        "std",
        &contradiction_theory(
            r#"axiom 已批准 : 批准 甲
  identity user_asserted
  source text "当事人主张" locator "起诉状""#,
        ),
    );

    let output = check(
        session(&theory, &[":why 批准 甲"]),
        GAP_OR_CONFLICT,
        &[
            "冲突未决：批准 甲",
            "「批准 甲」只是「用户陈述」，未经证明，不能自动胜过规则结论",
            "左：不批准 甲  ← 规则 ⟨拒绝⟩",
            "右：批准 甲  ← 事实〔用户陈述〕",
        ],
    );
    assert!(
        !stdout(&output).contains("推导已通过独立校验。"),
        "an unresolved conflict must not print the success line:\n{}",
        stdout(&output)
    );

    let certificate = check(session(&theory, &[":cert 批准 甲"]), GAP_OR_CONFLICT, &[]);
    let certificate = certificate_json(&certificate);
    assert_eq!(certificate.conflicts.len(), 1);
    let resolution = &certificate.conflicts[0].resolution;
    let std_deduce_cert::Resolution::Unresolved { reason } = resolution else {
        panic!("the claim-versus-rule conflict must stay unresolved: {resolution:?}");
    };
    let std_deduce_cert::UnresolvedReason::NonStrictFact { identity } = reason else {
        panic!("the reason must be non_strict_fact: {reason:?}");
    };
    assert_eq!(*identity, FactIdentity::UserAsserted);
    assert_eq!(
        assumption_identity(&certificate, "批准 甲"),
        FactIdentity::UserAsserted
    );

    let checked = verify_cert(&theory, "claim-vs-rule", &certificate);
    check(
        checked,
        GAP_OR_CONFLICT,
        &["逻辑校验：通过", "未决冲突 1 项"],
    );
}

/// Two claims against each other are both unproved: the conflict stays
/// unresolved for that reason, in `:why` and in the certificate.
#[test]
fn two_claims_conflict_without_a_winner() {
    let theory = TempFile::new(
        "two-claims",
        "std",
        r#"
sort 申请
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
contrary 批准 不批准
obj 甲 : 申请
axiom 已批准 : 批准 甲
  source text "当事人主张" locator "起诉状"
axiom 未批准 : 不批准 甲
  source text "对方主张" locator "答辩状"
"#,
    );

    check(
        session(&theory, &[":why 批准 甲"]),
        GAP_OR_CONFLICT,
        &[
            "冲突未决：批准 甲",
            "原因：两侧都只是主张，未经证明，不能判出一方胜出",
        ],
    );

    let certificate = check(session(&theory, &[":cert 批准 甲"]), GAP_OR_CONFLICT, &[]);
    let certificate = certificate_json(&certificate);
    let resolution = &certificate.conflicts[0].resolution;
    let std_deduce_cert::Resolution::Unresolved { reason } = resolution else {
        panic!("two claims must stay unresolved: {resolution:?}");
    };
    assert!(matches!(
        reason,
        std_deduce_cert::UnresolvedReason::ConflictingAssumptions
    ));
    for proposition in ["批准 甲", "不批准 甲"] {
        assert_eq!(
            assumption_identity(&certificate, proposition),
            FactIdentity::UserAsserted
        );
    }
}

/// A version 6 certificate edited back to version 4 is refused by the version
/// probe before any proof layer runs.
#[test]
fn a_version_4_certificate_is_rejected() {
    let theory = TempFile::new(
        "version-4",
        "std",
        r#"
sort 公民
pred 违法 : 公民 → Prop
obj 张三 : 公民
axiom 违法事实 : 违法 张三
  identity verified
  source text "判决" locator "第一页"
"#,
    );
    let generated = check(session(&theory, &[":cert 违法 张三"]), PROVED, &[]);
    let certificate = certificate_json(&generated);
    let json = certificate.to_json_pretty().unwrap();
    let old = json.replacen("\"format_version\": 8", "\"format_version\": 4", 1);
    assert_ne!(old, json, "the generated certificate must be version 6");
    let file = TempFile::new("version-4", "json", &old);

    let checked = session(&theory, &[&format!(":verify-cert {}", file.path.display())]);
    let checked = check(
        checked,
        ERROR,
        &["环境校验：未运行（证书 JSON 无效）", "逻辑校验：未运行"],
    );
    check_stderr(checked, ERROR, &["不是有效的证书 JSON", "supports 8"]);
}

/// Changing a claim's recorded identity to a strict one is caught by the
/// logical layer: the resolution says the fact is merely asserted, but the
/// assumption table says the court found it.
#[test]
fn a_tampered_identity_is_rejected() {
    let theory = TempFile::new(
        "tampered-identity",
        "std",
        &contradiction_theory(
            r#"axiom 已批准 : 批准 甲
  identity user_asserted
  source text "当事人主张" locator "起诉状""#,
        ),
    );
    let generated = check(session(&theory, &[":cert 批准 甲"]), GAP_OR_CONFLICT, &[]);
    let mut certificate = certificate_json(&generated);
    let assumption = certificate
        .assumptions
        .iter_mut()
        .find(|assumption| {
            std_deduce_kernel::pretty::print_expr(&std_deduce_kernel::Expr::from(
                &assumption.proposition,
            )) == "批准 甲"
        })
        .expect("the claim is recorded as an assumption");
    assumption.identity = FactIdentity::Verified;

    let checked = verify_cert(&theory, "tampered-identity", &certificate);
    let checked = check(checked, ERROR, &["逻辑校验：失败", "内核证明：未运行"]);
    check_stderr(
        checked,
        ERROR,
        &[
            "证书校验失败（逻辑层）",
            "在环境中登记为「用户陈述」",
            "证书写作「法院查明」",
        ],
    );
}

/// `:given` may not relabel a proposition the environment already registers
/// as a strict fact: one proposition has one identity.
#[test]
fn a_given_fact_cannot_change_a_verified_identity() {
    let theory = TempFile::new(
        "given-vs-verified",
        "std",
        r#"
sort 公民
pred 批准 : 公民 → Prop
obj 张三 : 公民
axiom 已批准 : 批准 张三
  identity verified
  source text "判决" locator "第一页"
"#,
    );
    let output = session(&theory, &[":given 批准 张三"]);
    let checked = check_stderr(
        output,
        ERROR,
        &[
            "同一命题只能有一种事实身份",
            "已登记为法院查明",
            "不能同时是用户陈述",
        ],
    );
    assert!(
        !stdout(&checked).contains("已登记用户陈述"),
        "a failed registration must not print the success line:\n{}",
        stdout(&checked)
    );
}

/// `:fact add` and `:fact assumed` are two identities for the same
/// proposition: the second registration is refused before it inserts anything.
/// Registering the same identity twice is allowed.
#[test]
fn a_session_fact_cannot_change_its_identity() {
    let theory = TempFile::new(
        "session-fact-identities",
        "std",
        r#"
sort 公民
pred 违规 : 公民 → Prop
obj 李四 : 公民
"#,
    );
    let output = session(&theory, &[":fact assumed 违规 李四", ":fact add 违规 李四"]);
    let checked = check_stderr(
        output,
        ERROR,
        &[
            "同一命题只能有一种事实身份",
            "已登记为分析假设",
            "不能同时是用户陈述",
        ],
    );
    let out = stdout(&checked);
    assert_eq!(
        out.matches("已登记用户陈述：违规 李四").count(),
        0,
        "the failed second registration must not print a success line:\n{out}"
    );

    // The same identity is not a conflict, even with two declarations.
    let output = session(&theory, &[":fact add 违规 李四", ":fact add 违规 李四"]);
    let out = check(output, PROVED, &["已登记用户陈述：违规 李四"]);
    assert_eq!(
        stdout(&out).matches("已登记用户陈述：违规 李四").count(),
        2,
        "two declarations with one identity are allowed:\n{}",
        stdout(&out)
    );
}

/// A gap names the identity of the fact blocking its candidate rule: the
/// same fact under a different identity would call for different work.
#[test]
fn a_gap_shows_the_identity_of_its_blocking_fact() {
    let theory = TempFile::new(
        "gap-blocker-identity",
        "std",
        r#"
sort 公民
pred 违法 : 公民 → Prop
pred 应受处罚 : 公民 → Prop
pred 轻微 : 公民 → Prop
obj 张三 : 公民
rule 处罚 :
  params x : 公民
  premise 违法 x
  conclude 应受处罚 x
  unless 轻微 x
  source text "处罚法" locator "第一条"
"#,
    );
    check(
        session(&theory, &[":fact add 轻微 张三", ":gap 应受处罚 张三"]),
        GAP_OR_CONFLICT,
        &[
            "无法推出 应受处罚 张三",
            "被阻断：「轻微 张三」〔用户陈述〕已成立，故本规则不触发",
        ],
    );
    // `:why` renders the gap from the certificate; the assumption table is
    // the identity record there, and the same fact must be named.
    check(
        session(&theory, &[":fact add 轻微 张三", ":why 应受处罚 张三"]),
        GAP_OR_CONFLICT,
        &[
            "? 应受处罚 张三  【未闭合】",
            "被阻断：「轻微 张三」〔用户陈述〕已成立",
        ],
    );
}

/// A session fact is a user assertion: `:inspect` labels the declaration with
/// its identity and `:why` renders the same identity on the assumption line.
#[test]
fn a_session_fact_shows_its_identity_in_inspect_and_why() {
    let theory = TempFile::new(
        "session-fact-identity",
        "std",
        r#"
sort 公民
pred 违法 : 公民 → Prop
pred 违规 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
"#,
    );
    let output = check(
        session(
            &theory,
            &[
                ":given 违法 张三",
                ":fact add 违规 李四",
                ":inspect",
                ":why 违法 张三",
                ":why 违规 李四",
            ],
        ),
        PROVED,
        &[
            "已登记用户陈述：违法 张三",
            "已登记用户陈述：违规 李四",
            " : 违法 张三  〔用户陈述〕",
            " : 违规 李四  〔用户陈述〕",
            "· 违法 张三  〔用户陈述〕",
            "· 违规 李四  〔用户陈述〕",
            "推导已通过独立校验",
        ],
    );
    let count = stdout(&output).matches("〔用户陈述〕").count();
    assert!(
        count >= 4,
        "both inspect lines and both assumption lines must show the identity:\n{}",
        stdout(&output)
    );
}
