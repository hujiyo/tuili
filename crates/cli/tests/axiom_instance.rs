//! End-to-end tests for universal elimination (certificate v8).
//!
//! A `axiom … : ∀ (x : T), P x` declaration is a universal fact. The reasoner
//! instantiates it on demand: a goal or a rule premise whose predicate matches
//! the declaration's body supplies the value of every binding variable, so no
//! object is enumerated. The certificate records one `axiom_instance` node per
//! instance and `:verify-cert` recomputes it from the kernel declaration.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use std_deduce_cert::{Binding, Certificate, Node};
use std_deduce_kernel::term::is_closed;
use std_deduce_kernel::Expr;

const PROVED: i32 = 0;
const GAP: i32 = 1;
const ERROR: i32 = 2;

const CITIZEN: &str = r#"
sort 公民
pred 受教育权利 : 公民 → Prop
axiom 凡公民皆有受教育权 : ∀ (p : 公民), 受教育权利 p
  source text "示例法" locator "第一条"
obj 张三 : 公民
obj 李四 : 公民
"#;

const RELATION: &str = r#"
sort 人
pred 关系 : 人 → 人 → Prop
axiom 人人有关系 : ∀ (x : 人), ∀ (y : 人), 关系 x y
  source text "示例法" locator "第一条"
pred 晴朗 : Prop
axiom 今天晴朗 : 晴朗
  source text "示例法" locator "第二条"
obj 甲 : 人
obj 乙 : 人
"#;

const ALIAS_SCOPE: &str = r#"
sort 公民
pred 受教育权利 : 公民 → Prop
def 教育权 : 公民 → Prop := 受教育权利
pred 登记在册 : 公民 → Prop
pred 获得保障 : 公民 → Prop
axiom 凡公民皆有受教育权 : ∀ (p : 公民), 受教育权利 p
  source text "示例法" locator "第一条"
obj 张三 : 公民
axiom 张三登记在册 : 登记在册 张三
  source text "案件材料" locator "第一页"
  occurred_at 2020-05-06
  occurred_in CN-HN
rule 教育保障 :
  params p : 公民
  premise 登记在册 p
  premise 教育权 p
  conclude 获得保障 p
  effective 1999-01-01
  jurisdiction CN
  territory CN-HN
  source text "测试法" locator "第一条"
"#;

const CONFLICT: &str = r#"
sort 人
pred 有罪 : 人 → Prop
pred 无罪 : 人 → Prop
contrary 有罪 无罪
axiom 凡人有罪 : ∀ (x : 人), 有罪 x
  source text "示例法" locator "第一条"
obj 张三 : 人
axiom 张三无罪 : 无罪 张三
  identity verified
  source text "判决书" locator "查明事实"
"#;

const DROPPED_BINDER: &str = r#"
sort 公民
pred 关系 : 公民 → 公民 → Prop
def 恒等 : 公民 → 公民 → 公民 := λ (a : 公民) := λ (b : 公民) := a
obj 甲 : 公民
axiom 都有关系 : ∀ (x : 公民), ∀ (y : 公民), 关系 (恒等 x y) 甲
  source text "示例法" locator "第一条"
"#;

const OPEN_PREMISE_ISSUE: &str = r#"
sort 公民
pred 受教育权利 : 公民 → Prop
def 教育权 : 公民 → Prop := 受教育权利
pred 获得保障 : 公民 → Prop
axiom 凡公民皆有受教育权 : ∀ (p : 公民), 受教育权利 p
  source text "示例法" locator "第一条"
obj 张三 : 公民
rule 教育保障 :
  params p : 公民
  premise 教育权 p
  conclude 获得保障 p
  source text "测试法" locator "第一条"
"#;

fn run(commands: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .args(commands)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

fn session(theory: &Path, commands: &[String]) -> Output {
    let mut all = vec![format!(":load {}", theory.display())];
    all.extend_from_slice(commands);
    run(&all)
}

fn session_with_jurisdiction(theory: &Path, commands: &[String]) -> Output {
    let mut all = vec!["--jurisdiction".to_owned(), "CN".to_owned()];
    all.push(format!(":load {}", theory.display()));
    all.extend_from_slice(commands);
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

/// The raw certificate JSON: `:load` prints its report first, so the document
/// starts at the first `{`.
fn certificate_text(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    text[start..].trim_end().to_owned()
}

fn certificate(output: &Output) -> Certificate {
    let text = certificate_text(output);
    Certificate::from_json(&text).unwrap_or_else(|e| panic!("invalid certificate JSON:\n{e}"))
}

fn generated_certificate(theory: &Path, goal: &str) -> Certificate {
    let output = session(theory, &[format!(":cert {goal}")]);
    assert_exit(&output, PROVED);
    certificate(&output)
}

fn generated_certificate_with_jurisdiction(theory: &Path, goal: &str) -> Certificate {
    let output = session_with_jurisdiction(theory, &[format!(":cert {goal}")]);
    assert_exit(&output, PROVED);
    certificate(&output)
}

fn axiom_instance_node(certificate: &Certificate) -> &Node {
    certificate
        .nodes
        .iter()
        .find(|node| matches!(node, Node::AxiomInstance { .. }))
        .unwrap_or_else(|| panic!("the certificate has no axiom_instance node"))
}

fn axiom_instance_conclusions(certificate: &Certificate) -> Vec<&Node> {
    certificate
        .nodes
        .iter()
        .filter(|node| matches!(node, Node::AxiomInstance { .. }))
        .collect()
}

/// A temporary file removed when the test ends (including on panic).
struct TempFile {
    path: PathBuf,
}

impl TempFile {
    fn new(tag: &str, extension: &str, contents: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-axiom-{}-{tag}-{n}.{extension}",
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

#[test]
fn a_universal_axiom_proves_an_atom_and_why_shows_the_instance() {
    let theory = TempFile::new("citizen", "std", CITIZEN);
    let why = session(&theory.path, &[":why 受教育权利 张三".to_owned()]);
    assert_exit(&why, PROVED);
    let out = stdout(&why);
    assert!(
        out.contains("〈公理 凡公民皆有受教育权〔用户陈述〕〉"),
        "the step must name the universal fact and its identity:\n{out}"
    );
    assert!(
        out.contains("p ↦ 张三"),
        "the binding must be printed:\n{out}"
    );
    assert!(out.contains("推导已通过独立校验。"), "{out}");
    assert!(
        out.contains("信任：依赖假设"),
        "the universal fact is user asserted, not a strict fact:\n{out}"
    );

    let explain = session(&theory.path, &[":explain 受教育权利 张三".to_owned()]);
    assert_exit(&explain, PROVED);
    let narrative = stdout(&explain);
    assert!(
        narrative.contains("根据全称公理「凡公民皆有受教育权」（用户陈述）的全称实例"),
        "the narrative must call the step a universal instance:\n{narrative}"
    );

    // `:gap` is consistent with `:why`: the goal is reachable, and the axiom
    // instance is named with the binding it used.
    let gap = session(&theory.path, &[":gap 受教育权利 张三".to_owned()]);
    assert_exit(&gap, PROVED);
    let out = stdout(&gap);
    assert!(out.contains("目标可以推出。"), "{out}");
    assert!(
        out.contains("由全称公理 ⟨凡公民皆有受教育权⟩ 实例化（p := 张三）"),
        "{out}"
    );
}

#[test]
fn a_two_binder_universal_instantiates_both_values_without_leaking_variables() {
    let theory = TempFile::new("relation", "std", RELATION);
    let why = session(&theory.path, &[":why 关系 甲 乙".to_owned()]);
    assert_exit(&why, PROVED);
    let out = stdout(&why);
    assert!(
        out.contains("实例：x ↦ 甲，y ↦ 乙"),
        "both binders must be recorded in order:\n{out}"
    );

    let certificate = generated_certificate(&theory.path, "关系 甲 乙");
    assert_eq!(certificate.format_version.get(), 8);
    let instance = axiom_instance_node(&certificate);
    let Node::AxiomInstance {
        axiom,
        bindings,
        conclusion,
        ..
    } = instance
    else {
        unreachable!();
    };
    assert_eq!(axiom, "人人有关系");
    assert_eq!(
        bindings,
        &[
            Binding {
                parameter: "x".to_owned(),
                value: std_deduce_cert::CertExpr::Const {
                    name: "甲".to_owned()
                },
            },
            Binding {
                parameter: "y".to_owned(),
                value: std_deduce_cert::CertExpr::Const {
                    name: "乙".to_owned()
                },
            },
        ]
    );
    let conclusion = Expr::from(conclusion);
    assert!(
        is_closed(&conclusion),
        "the instance conclusion must have no free variable (no leaked x/y): {conclusion}"
    );
}

#[test]
fn the_instance_certificate_is_byte_stable_and_verifies_in_another_session() {
    let theory = TempFile::new("relation", "std", RELATION);
    let first = session(&theory.path, &[":cert 关系 甲 乙".to_owned()]);
    assert_exit(&first, PROVED);
    let second = session(&theory.path, &[":cert 关系 甲 乙".to_owned()]);
    assert_exit(&second, PROVED);
    assert_eq!(
        certificate_text(&first),
        certificate_text(&second),
        "two runs on the same case must produce the same certificate bytes"
    );

    let certificate = TempFile::new("relation-cert", "json", &certificate_text(&first));
    let verified = session(
        &theory.path,
        &[format!(
            ":verify-cert \"{}\" 关系 甲 乙",
            certificate.path.display()
        )],
    );
    assert_exit(&verified, PROVED);
    let out = stdout(&verified);
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("根为公理实例推导"), "{out}");
    assert!(out.contains("内核证明：通过"), "{out}");
    assert!(out.contains("目标绑定：通过"), "{out}");
}

#[test]
fn a_forged_binding_or_conclusion_is_rejected() {
    let theory = TempFile::new("relation", "std", RELATION);
    let base = generated_certificate(&theory.path, "关系 甲 乙");

    let mut changed_binding = base.clone();
    // Mutate the first binder value in place.
    for node in &mut changed_binding.nodes {
        if let Node::AxiomInstance { bindings, .. } = node {
            bindings[0].value = std_deduce_cert::CertExpr::Const {
                name: "乙".to_owned(),
            };
        }
    }
    assert_verify_rejects(&theory.path, &changed_binding, "按绑定得到的结论是");

    let mut changed_conclusion = base.clone();
    for node in &mut changed_conclusion.nodes {
        if let Node::AxiomInstance { conclusion, .. } = node {
            *conclusion = std_deduce_cert::CertExpr::App {
                func: Box::new(std_deduce_cert::CertExpr::App {
                    func: Box::new(std_deduce_cert::CertExpr::Const {
                        name: "关系".to_owned(),
                    }),
                    arg: Box::new(std_deduce_cert::CertExpr::Const {
                        name: "甲".to_owned(),
                    }),
                }),
                arg: Box::new(std_deduce_cert::CertExpr::Const {
                    name: "甲".to_owned(),
                }),
            };
        }
    }
    assert_verify_rejects(&theory.path, &changed_conclusion, "按绑定得到的结论是");

    let mut open_value = base.clone();
    for node in &mut open_value.nodes {
        if let Node::AxiomInstance { bindings, .. } = node {
            bindings[0].value = std_deduce_cert::CertExpr::Var { index: 0 };
        }
    }
    assert_verify_rejects(&theory.path, &open_value, "不是闭合项");

    let mut unknown_axiom = base.clone();
    for node in &mut unknown_axiom.nodes {
        if let Node::AxiomInstance { axiom, .. } = node {
            *axiom = "不存在的公理".to_owned();
        }
    }
    assert_verify_rejects(&theory.path, &unknown_axiom, "未知全称公理");

    let mut forged_identity = base;
    for node in &mut forged_identity.nodes {
        if let Node::AxiomInstance { identity, .. } = node {
            *identity = std_deduce_cert::FactIdentity::Verified;
        }
    }
    assert_verify_rejects(&theory.path, &forged_identity, "本步记录的是「法院查明」");
}

#[test]
fn a_non_universal_declaration_cannot_be_claimed_as_an_instance() {
    let theory = TempFile::new("relation", "std", RELATION);
    let base = generated_certificate(&theory.path, "关系 甲 乙");
    let mut forged = base;
    for node in &mut forged.nodes {
        if let Node::AxiomInstance {
            axiom,
            bindings,
            conclusion,
            ..
        } = node
        {
            *axiom = "今天晴朗".to_owned();
            *bindings = Vec::new();
            *conclusion = std_deduce_cert::CertExpr::Const {
                name: "晴朗".to_owned(),
            };
        }
    }
    assert_verify_rejects(&theory.path, &forged, "不是带命名绑定变量的全称命题");
}

fn assert_verify_rejects(theory: &Path, forged: &Certificate, expected: &str) {
    let file = TempFile::new(
        "forged",
        "json",
        &forged
            .to_json_pretty()
            .unwrap_or_else(|e| panic!("serialize forged certificate: {e}")),
    );
    let output = session(
        theory,
        &[format!(":verify-cert \"{}\"", file.path.display())],
    );
    assert_exit(&output, ERROR);
    let out = stdout(&output);
    let err = stderr(&output);
    assert!(
        out.contains(expected) || err.contains(expected),
        "expected `{expected}` in the verification output:\nstdout:\n{out}\nstderr:\n{err}"
    );
}

#[test]
fn a_gap_reports_the_universal_fact_and_why_it_cannot_be_instantiated() {
    // The declaration's body drops `y` (`恒等 x y` unfolds to `x`). The goal
    // determines `x` but not `y`, and the engine must not invent a value for
    // it: the gap lists the universal fact and says the binding is incomplete.
    let theory = TempFile::new("dropped-binder", "std", DROPPED_BINDER);
    let gap = session(&theory.path, &[":gap 关系 甲 甲".to_owned()]);
    assert_exit(&gap, GAP);
    let out = stdout(&gap);
    assert!(out.contains("公理候选 ⟨都有关系⟩"), "{out}");
    assert!(
        out.contains("公理体的绑定没有覆盖每个绑定变量"),
        "the refusal reason must name the incomplete binding:\n{out}"
    );

    let certificate_output = session(&theory.path, &[":cert 关系 甲 甲".to_owned()]);
    assert_exit(&certificate_output, GAP);
    let certificate = certificate(&certificate_output);
    let axiom_candidates = certificate
        .nodes
        .iter()
        .find_map(|node| match node {
            Node::Gap {
                axiom_candidates, ..
            } => Some(axiom_candidates),
            _ => None,
        })
        .expect("the certificate records the gap");
    assert_eq!(axiom_candidates.len(), 1);
    assert_eq!(axiom_candidates[0].axiom, "都有关系");
    assert!(
        axiom_candidates[0].problem.is_some(),
        "the refusal is recorded"
    );

    // The gap certificate is still a valid certificate: the checker recomputes
    // the axiom candidate and fails only the root, not the format.
    let file = TempFile::new(
        "gap-cert",
        "json",
        &certificate
            .to_json_pretty()
            .expect("the certificate serializes"),
    );
    let verified = session(
        &theory.path,
        &[format!(":verify-cert \"{}\"", file.path.display())],
    );
    assert_exit(&verified, GAP);
    assert!(
        stdout(&verified).contains("逻辑校验：通过"),
        "{}",
        stdout(&verified)
    );
}

#[test]
fn an_axiom_instance_satisfies_a_rule_premise_with_a_def_alias_and_scope() {
    let theory = TempFile::new("alias-scope", "std", ALIAS_SCOPE);
    let why = session_with_jurisdiction(&theory.path, &[":why 获得保障 张三".to_owned()]);
    assert_exit(&why, PROVED);
    let out = stdout(&why);
    assert!(
        out.contains("⟨教育保障⟩"),
        "the rule must fire on the axiom-provided premise:\n{out}"
    );
    assert!(
        out.contains("〈公理 凡公民皆有受教育权"),
        "the premise must be proved by the universal instance:\n{out}"
    );
    assert!(out.contains("推导已通过独立校验。"), "{out}");

    let certificate = generated_certificate_with_jurisdiction(&theory.path, "获得保障 张三");
    let file = TempFile::new(
        "alias-cert",
        "json",
        &certificate
            .to_json_pretty()
            .expect("the certificate serializes"),
    );
    let verified = session_with_jurisdiction(
        &theory.path,
        &[format!(
            ":verify-cert \"{}\" 获得保障 张三",
            file.path.display()
        )],
    );
    assert_exit(&verified, PROVED);
    let out = stdout(&verified);
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(out.contains("适用性重算"), "{out}");
    assert!(out.contains("目标绑定：通过"), "{out}");
}

#[test]
fn issues_report_the_universal_fact_for_a_premise_the_order_did_not_demand() {
    // The rule mentions its parameterised premise first, so backtracking sees
    // an open pattern and cannot demand the universal instance. The issue scan
    // must still explain that the missing premise is obtainable from the
    // universal fact, with the binding it would need.
    let theory = TempFile::new("open-premise", "std", OPEN_PREMISE_ISSUE);
    let issues = session(&theory.path, &[":issues".to_owned()]);
    assert_exit(&issues, GAP);
    let out = stdout(&issues);
    assert!(out.contains("获得保障 张三"), "{out}");
    assert!(
        out.contains("公理候选 ⟨凡公民皆有受教育权⟩（绑定：p := 张三）"),
        "{out}"
    );
    assert!(
        out.contains("可由该全称公理实例化；当前推导没有触发它"),
        "{out}"
    );
}

#[test]
fn an_axiom_instance_loses_to_a_strict_fact_and_the_conflict_is_checked() {
    let theory = TempFile::new("conflict", "std", CONFLICT);
    let why = session(&theory.path, &[":why 有罪 张三".to_owned()]);
    assert_exit(&why, GAP);
    let out = stdout(&why);
    assert!(out.contains("冲突已裁决"), "{out}");
    assert!(
        out.contains("本结论「有罪 张三」被否决"),
        "the instance side is the defeated one:\n{out}"
    );
    assert!(
        out.contains("胜出的是「无罪 张三」（事实〔法院查明〕）"),
        "{out}"
    );

    let certificate_output = session(&theory.path, &[":cert 有罪 张三".to_owned()]);
    assert_exit(&certificate_output, GAP);
    let certificate = certificate(&certificate_output);
    assert_eq!(certificate.conflicts.len(), 1);
    assert!(
        matches!(
            certificate.conflicts[0].left_by,
            std_deduce_cert::Provenance::Axiom { .. }
        ) || matches!(
            certificate.conflicts[0].right_by,
            std_deduce_cert::Provenance::Axiom { .. }
        )
    );
    // The certificate records a universal-elimination node for the defeated
    // side too, so both sides of the conflict can be inspected.
    assert!(
        !axiom_instance_conclusions(&certificate).is_empty(),
        "the defeated instance must still have a node"
    );

    let file = TempFile::new(
        "conflict-cert",
        "json",
        &certificate
            .to_json_pretty()
            .expect("the certificate serializes"),
    );
    let verified = session(
        &theory.path,
        &[format!(":verify-cert \"{}\"", file.path.display())],
    );
    // The root is a gap, so the command reports a gap, but the certificate's
    // conflict resolution (including the axiom provenance) must pass both
    // layers.
    assert_exit(&verified, GAP);
    let out = stdout(&verified);
    assert!(out.contains("逻辑校验：通过"), "{out}");
    assert!(
        out.contains("冲突未决 0 项") || out.contains("未决冲突 0 项"),
        "{out}"
    );
}
