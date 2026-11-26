//! End-to-end tests for disjunctive and existential rule premises (certificate
//! v13).
//!
//! A disjunctive premise needs one written branch proved; an existential premise
//! needs one concrete declared individual whose body is proved. The selection is
//! derived from the actual proof, recorded in the certificate, and re-checked by
//! `:verify-cert`: an unproved branch, an out-of-range branch and an invented
//! witness are all rejected.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_cert::{Certificate, Node, PremiseChoice};

const PROVED: i32 = 0;
const GAP: i32 = 1;
const ERROR: i32 = 2;

fn run(commands: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .args(commands)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
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

fn certificate_text(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    text[start..].trim_end().to_owned()
}

fn certificate_json(output: &Output) -> Certificate {
    let text = certificate_text(output);
    Certificate::from_json(&text)
        .unwrap_or_else(|e| panic!("invalid certificate JSON:\n{e}\nstdout:\n{text}"))
}

fn temp_path(tag: &str, extension: &str) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "std-deduce-or-exists-{}-{tag}-{n}.{extension}",
        std::process::id()
    ))
}

struct TempFile {
    path: PathBuf,
}

impl TempFile {
    fn new(tag: &str, extension: &str, contents: &str) -> Self {
        let path = temp_path(tag, extension);
        fs::write(&path, contents).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempFile { path }
    }

    fn path_text(&self) -> String {
        self.path.display().to_string()
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn session(file: &TempFile, commands: &[String]) -> Output {
    let mut all = vec![format!(":load {}", file.path_text())];
    all.extend_from_slice(commands);
    run(all)
}

const THEORY: &str = r#"
sort 人
obj 甲 : 人
obj 乙 : 人
obj 丙 : 人
pred 配偶 : 人 → 人 → Prop
pred 有情 : 人 → 人 → Prop
pred 有配偶 : 人 → Prop

axiom 婚一 : 配偶 乙 甲
source text "测试" locator "一"
axiom 婚二 : 配偶 甲 丙
source text "测试" locator "二"

rule 配偶规则 :
  params p : 人, q : 人
  premise 配偶 p q or 配偶 q p
  conclude 有情 p q
  source text "测试" locator "三"

rule 有配偶规则 :
  params p : 人
  premise exists x : 人, 配偶 p x
  conclude 有配偶 p
  source text "测试" locator "四"
"#;

const NO_BRANCH_THEORY: &str = r#"
sort 人
obj 甲 : 人
obj 乙 : 人
obj 丙 : 人
pred 配偶 : 人 → 人 → Prop
pred 有情 : 人 → 人 → Prop

axiom 婚一 : 配偶 乙 甲
source text "测试" locator "一"

rule 配偶规则 :
  params p : 人, q : 人
  premise 配偶 p q or 配偶 q p
  conclude 有情 p q
  source text "测试" locator "三"
"#;

/// Two facts give 甲 two witnesses (乙 and 丙); 丙 itself has none.
const EXISTS_THEORY: &str = r#"
sort 人
obj 甲 : 人
obj 乙 : 人
obj 丙 : 人
pred 配偶 : 人 → 人 → Prop
pred 有配偶 : 人 → Prop

axiom 婚一 : 配偶 甲 乙
source text "测试" locator "一"
axiom 婚二 : 配偶 甲 丙
source text "测试" locator "二"

rule 有配偶规则 :
  params p : 人
  premise exists x : 人, 配偶 p x
  conclude 有配偶 p
  source text "测试" locator "四"
"#;

fn write_certificate(tag: &str, text: &str) -> TempFile {
    TempFile::new(tag, "json", text)
}

fn verify(file: &TempFile, certificate: &TempFile, goal: &str) -> Output {
    session(
        file,
        &[format!(":verify-cert {} {goal}", certificate.path_text())],
    )
}

#[test]
fn a_disjunction_fires_when_only_the_second_branch_holds_and_records_it() {
    let theory = TempFile::new("or", "std", THEORY);
    let output = session(&theory, &[":cert 有情 甲 乙".to_owned()]);
    assert_exit(&output, PROVED);
    let certificate = certificate_json(&output);
    assert_eq!(certificate.format_version.get(), 13);

    // `有情 甲 乙` binds p := 甲, q := 乙, so branch 1 (`配偶 q p` = 配偶 乙 甲)
    // is the proof. Branch 0 (`配偶 甲 乙`) is false.
    let root = certificate.root.expect("a proved certificate has a root");
    let Node::RuleApplication { choices, .. } = &certificate.nodes[root] else {
        panic!("the root of 有情 甲 乙 is not a rule application");
    };
    assert!(
        choices
            .iter()
            .any(|choice| matches!(choice, PremiseChoice::Branch { branch: 1, .. })),
        "the root must record the second branch, got {choices:?}"
    );
    assert!(
        !choices
            .iter()
            .any(|choice| matches!(choice, PremiseChoice::Branch { branch: 0, .. })),
        "the root must not claim the unproved first branch: {choices:?}"
    );

    let certificate_file = write_certificate("or", &certificate_text(&output));
    assert_exit(&verify(&theory, &certificate_file, "有情 甲 乙"), PROVED);
}

#[test]
fn a_disjunction_whose_branches_all_fail_lists_each_branch_gap() {
    let theory = TempFile::new("or-gap", "std", NO_BRANCH_THEORY);
    let output = session(&theory, &[":gap 有情 乙 丙".to_owned()]);
    assert_exit(&output, GAP);
    let text = stdout(&output);
    assert!(
        text.contains("缺析取前提（2 个分支，按书写顺序）"),
        "the gap must name both branches, got:\n{text}"
    );
    assert!(text.contains("分支 1 ⟨配偶 乙 丙⟩"), "{text}");
    assert!(text.contains("分支 2 ⟨配偶 丙 乙⟩"), "{text}");
    assert!(
        !text.contains("缺 ⟨配偶 乙 丙 or 配偶 丙 乙⟩"),
        "a disjunction is not a lump-sum missing premise:\n{text}"
    );
}

#[test]
fn an_existential_premise_produces_one_instance_per_witness_and_records_them() {
    let theory = TempFile::new("exists", "std", EXISTS_THEORY);
    let output = session(&theory, &[":cert 有配偶 甲".to_owned()]);
    assert_exit(&output, PROVED);
    let certificate = certificate_json(&output);
    // The certificate may also prove 有配偶 乙 from the same premise; the group
    // for 有配偶 甲 contains both witnesses and each is recorded independently.
    let group = certificate
        .alternatives
        .iter()
        .find(|group| {
            format!("{:?}", group.proposition).contains("有配偶")
                && format!("{:?}", group.proposition).contains("甲")
        })
        .expect("有配偶 甲 must have an alternatives group");
    assert_eq!(group.witnesses.len(), 2, "two witnesses were found");
    let mut witnesses = Vec::new();
    for witness in &group.witnesses {
        if let Node::RuleApplication { choices, .. } = &certificate.nodes[*witness] {
            for choice in choices {
                if let PremiseChoice::Witness { witness, .. } = choice {
                    witnesses.push(format!("{witness:?}"));
                }
            }
        }
    }
    assert!(
        witnesses.iter().any(|witness| witness.contains("乙")),
        "witness 乙 must be recorded, got {witnesses:?}"
    );
    assert!(
        witnesses.iter().any(|witness| witness.contains("丙")),
        "witness 丙 must be recorded, got {witnesses:?}"
    );

    let certificate_file = write_certificate("exists", &certificate_text(&output));
    assert_exit(&verify(&theory, &certificate_file, "有配偶 甲"), PROVED);
}

#[test]
fn an_existential_premise_without_a_witness_explains_what_is_needed() {
    let theory = TempFile::new("exists-gap", "std", EXISTS_THEORY);
    let output = session(&theory, &[":gap 有配偶 丙".to_owned()]);
    assert_exit(&output, GAP);
    let text = stdout(&output);
    assert!(
        text.contains("存在前提：需要某个已声明个体满足"),
        "an existence gap must say that some individual is needed:\n{text}"
    );
    assert!(
        text.contains("候选个体"),
        "the declared candidate individuals must be listed:\n{text}"
    );
}

#[test]
fn a_tampered_branch_choice_is_rejected() {
    let theory = TempFile::new("or-tamper", "std", THEORY);
    let output = session(&theory, &[":cert 有情 甲 乙".to_owned()]);
    assert_exit(&output, PROVED);
    let mut certificate = certificate_json(&output);
    let mut tampered = false;
    for node in &mut certificate.nodes {
        if let Node::RuleApplication { choices, .. } = node {
            for choice in choices {
                if let PremiseChoice::Branch { branch, .. } = choice {
                    if *branch == 1 {
                        *branch = 0;
                        tampered = true;
                    }
                }
            }
        }
    }
    assert!(tampered, "the fixture certificate must record branch 1");
    let text = certificate.to_json().unwrap();
    let certificate_file = write_certificate("or-tamper", &text);
    let verified = verify(&theory, &certificate_file, "有情 甲 乙");
    assert_exit(&verified, ERROR);
    assert!(
        stderr(&verified).contains("析取分支"),
        "the rejection must name the branch: {}",
        stderr(&verified)
    );
}

#[test]
fn an_out_of_range_branch_choice_is_rejected() {
    let theory = TempFile::new("or-oob", "std", THEORY);
    let output = session(&theory, &[":cert 有情 甲 乙".to_owned()]);
    assert_exit(&output, PROVED);
    let mut certificate = certificate_json(&output);
    for node in &mut certificate.nodes {
        if let Node::RuleApplication { choices, .. } = node {
            for choice in choices {
                if let PremiseChoice::Branch { branch, .. } = choice {
                    *branch = 9;
                }
            }
        }
    }
    let certificate_file = write_certificate("or-oob", &certificate.to_json().unwrap());
    let verified = verify(&theory, &certificate_file, "有情 甲 乙");
    assert_exit(&verified, ERROR);
    assert!(
        stderr(&verified).contains("只有 2 个分支"),
        "the rejection must name the written branch count: {}",
        stderr(&verified)
    );
}

#[test]
fn a_witness_that_is_not_a_declared_individual_is_rejected() {
    let theory = TempFile::new("exists-tamper", "std", EXISTS_THEORY);
    let output = session(&theory, &[":cert 有配偶 甲".to_owned()]);
    assert_exit(&output, PROVED);
    let mut certificate = certificate_json(&output);
    let mut tampered = false;
    for node in &mut certificate.nodes {
        if let Node::RuleApplication { choices, .. } = node {
            for choice in choices {
                if let PremiseChoice::Witness { witness, .. } = choice {
                    *witness = std_deduce_cert::CertExpr::Const {
                        name: "不存在".to_owned(),
                    };
                    tampered = true;
                }
            }
        }
    }
    assert!(tampered, "the fixture certificate must record a witness");
    let certificate_file = write_certificate("exists-tamper", &certificate.to_json().unwrap());
    let verified = verify(&theory, &certificate_file, "有配偶 甲");
    assert_exit(&verified, ERROR);
    assert!(
        stderr(&verified).contains("不是已声明个体"),
        "the rejection must name the invented witness: {}",
        stderr(&verified)
    );
}

#[test]
fn a_v10_or_v11_certificate_is_rejected_by_the_version_probe() {
    let theory = TempFile::new("version", "std", THEORY);
    let output = session(&theory, &[":cert 有情 甲 乙".to_owned()]);
    assert_exit(&output, PROVED);
    let text = certificate_text(&output);
    for old in [10, 11, 12] {
        let downgraded = text.replace(
            "\"format_version\": 13",
            &format!("\"format_version\": {old}"),
        );
        let certificate_file = write_certificate("version", &downgraded);
        let verified = verify(&theory, &certificate_file, "有情 甲 乙");
        assert_exit(&verified, ERROR);
        let message = stderr(&verified);
        assert!(
            message.contains(&format!("unsupported certificate format version {old}"))
                && message.contains("this build supports 13"),
            "the version probe must reject v{old}: {message}"
        );
    }
}

#[test]
fn too_many_branches_are_refused_at_load_time() {
    let mut source = String::from(
        "sort 人\nobj 甲 : 人\npred 配偶 : 人 → 人 → Prop\npred 有情 : 人 → 人 → Prop\n\
         axiom 婚 : 配偶 甲 甲\nsource text \"测试\" locator \"一\"\n\
         rule 配偶规则 :\n  params p : 人\n  premise ",
    );
    // Nine branches exceed the fixed eight-branch bound.
    source.push_str("配偶 p p");
    for _ in 0..8 {
        source.push_str(" or 配偶 p p");
    }
    source.push_str("\n  conclude 有情 p p\n  source text \"测试\" locator \"二\"\n");
    let theory = TempFile::new("branch-limit", "std", &source);
    let output = session(&theory, &[":why 有情 甲 甲".to_owned()]);
    assert_exit(&output, ERROR);
    assert!(
        stderr(&output).contains("超过每个析取前提 8 个分支的上限"),
        "the load error must name the branch bound: {}",
        stderr(&output)
    );
}

#[test]
fn nested_exists_is_refused_explicitly() {
    let source = r#"
sort 人
obj 甲 : 人
pred 配偶 : 人 → 人 → Prop
pred 有情 : 人 → Prop
rule 规则 :
  params p : 人
  premise exists x : 人, exists y : 人, 配偶 x y
  conclude 有情 p
  source text "测试" locator "一"
"#;
    let theory = TempFile::new("nested", "std", source);
    let output = session(&theory, &[":why 有情 甲".to_owned()]);
    assert_exit(&output, ERROR);
    assert!(
        stderr(&output).contains("嵌套量词暂不支持"),
        "nested quantifiers must be refused explicitly: {}",
        stderr(&output)
    );
}

#[test]
fn too_many_witness_candidates_fail_explicitly() {
    let mut source = String::from("sort 人\n");
    for index in 0..65 {
        source.push_str(&format!("obj 个体{index} : 人\n"));
    }
    source.push_str("obj 甲 : 人\npred 配偶 : 人 → 人 → Prop\npred 有配偶 : 人 → Prop\n");
    source.push_str("rule 有配偶规则 :\n  params p : 人\n  premise exists x : 人, 配偶 p x\n  conclude 有配偶 p\n  source text \"测试\" locator \"一\"\n");
    for index in 0..65 {
        source.push_str(&format!(
            "axiom 婚{index} : 配偶 甲 个体{index}\nsource text \"测试\" locator \"二\"\n"
        ));
    }
    let theory = TempFile::new("witness-limit", "std", &source);
    let output = session(&theory, &[":why 有配偶 甲".to_owned()]);
    assert_exit(&output, ERROR);
    assert!(
        stderr(&output).contains("见证候选超过每个前提 64 个上限"),
        "the witness limit must be explicit: {}",
        stderr(&output)
    );
}

#[test]
fn verify_cert_discloses_that_branch_choices_are_logical_side_conditions() {
    let theory = TempFile::new("disclosure", "std", THEORY);
    let output = session(&theory, &[":cert 有情 甲 乙".to_owned()]);
    assert_exit(&output, PROVED);
    let certificate_file = write_certificate("disclosure", &certificate_text(&output));
    let verified = verify(&theory, &certificate_file, "有情 甲 乙");
    assert_exit(&verified, PROVED);
    let text = stdout(&verified);
    assert!(
        text.contains("其中") && text.contains("步含析取/存在前提，分支选择由逻辑层复核"),
        "verify-cert must disclose the kernel coverage boundary:\n{text}"
    );
}

const PLAIN_THEORY: &str = r#"
sort 人
obj 甲 : 人
pred 安静 : 人 → Prop
pred 良好 : 人 → Prop
axiom 事实 : 安静 甲
source text "测试" locator "一"
rule 安静规则 :
  params p : 人
  premise 安静 p
  conclude 良好 p
  source text "测试" locator "二"
"#;

#[test]
fn verify_cert_without_compound_premises_keeps_the_kernel_line_byte_identical() {
    let theory = TempFile::new("plain", "std", PLAIN_THEORY);
    let output = session(&theory, &[":cert 良好 甲".to_owned()]);
    assert_exit(&output, PROVED);
    let certificate_file = write_certificate("plain", &certificate_text(&output));
    let verified = verify(&theory, &certificate_file, "良好 甲");
    assert_exit(&verified, PROVED);
    let text = stdout(&verified);
    assert!(
        text.contains("内核证明：通过（1 个规则步骤；根证明项通过内核）"),
        "the plain kernel line must be unchanged:\n{text}"
    );
    assert!(
        !text.contains("析取/存在前提"),
        "a plain certificate must not gain the disclosure:\n{text}"
    );
}

#[test]
fn why_labels_each_branch_of_a_failing_disjunction() {
    let theory = TempFile::new("or-why", "std", NO_BRANCH_THEORY);
    let output = session(&theory, &[":why 有情 乙 丙".to_owned()]);
    assert_exit(&output, GAP);
    let text = stdout(&output);
    assert!(text.contains("缺："), "{text}");
    assert!(text.contains("第 1 个分支"), "{text}");
    assert!(text.contains("第 2 个分支"), "{text}");
}

/// The v10 fixture is kept as a rejected sample: a version probe must refuse it
/// before reading any field. A v11 or v12 document is the same shape at an
/// older version, so the probe is exercised for all three.
#[test]
fn the_versions_below_the_current_one_are_rejected() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../crates/cert/tests/fixtures")
        .join("certificate_v10.json");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    for version in [10, 11, 12] {
        let sample = text.replace(
            "\"format_version\": 10",
            &format!("\"format_version\": {version}"),
        );
        let error = Certificate::from_json(&sample).unwrap_err().to_string();
        assert!(
            error.contains(&format!("unsupported certificate format version {version}")),
            "v{version}: {error}"
        );
    }
}
