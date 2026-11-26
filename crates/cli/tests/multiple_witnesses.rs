//! End-to-end tests for certificate v13's multiple-witness table.
//!
//! A conclusion derived by two rules keeps both derivations: `:why` says how
//! many other independent arguments exist, `:cert` records every witness node,
//! and `:verify-cert` checks each one. The tests mutate an exported
//! certificate and run the checker in a fresh process, so the guarantees are
//! tested on the wire format rather than on the reasoner's memory.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use std_deduce_cert::{CertExpr, Certificate, Node, Provenance, MAX_CERT_WITNESSES_PER_CONCLUSION};

const PROVED: i32 = 0;
const GAP: i32 = 1;
const ERROR: i32 = 2;

const TWO_RULES: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
obj 甲 : 人
axiom 事实 : P 甲
  source text "测试" locator "1"
rule 规则A :
  params x : 人
  premise P x
  conclude Q x
  source text "测试" locator "A"
rule 规则B :
  params x : 人
  premise P x
  conclude Q x
  source text "测试" locator "B"
"#;

/// Ten independent rules all concluding the same proposition.
fn ten_rules() -> String {
    let mut theory = String::from(
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
obj 甲 : 人
axiom 事实 : P 甲
  source text "测试" locator "1"
"#,
    );
    for name in [
        "规则A", "规则B", "规则C", "规则D", "规则E", "规则F", "规则G", "规则H", "规则I", "规则J",
    ] {
        theory.push_str(&format!(
            "rule {name} :\n  params x : 人\n  premise P x\n  conclude Q x\n  \
             source text \"测试\" locator \"{name}\"\n"
        ));
    }
    theory
}

/// Two rules argue for one side of a declared conflict, a third for the other.
const CONFLICT: &str = r#"
sort 人
pred P : 人 → Prop
pred 好 : 人 → Prop
pred 坏 : 人 → Prop
contrary 好 坏
obj 甲 : 人
axiom 事实 : P 甲
  source text "测试" locator "1"
rule 规则A :
  params x : 人
  premise P x
  conclude 好 x
  source text "测试" locator "A"
rule 规则B :
  params x : 人
  premise P x
  conclude 好 x
  source text "测试" locator "B"
rule 规则C :
  params x : 人
  premise P x
  conclude 坏 x
  source text "测试" locator "C"
"#;

/// A universal fact breaks the rule cycle: v8 proved `Q 甲` through the
/// universal instance and must keep doing so in v13.
const CYCLE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
obj 甲 : 人
axiom 全称 : ∀ (x : 人), Q x
  source text "测试" locator "1"
rule 规则S :
  params x : 人
  premise Q x
  conclude P x
  source text "测试" locator "S"
rule 规则R :
  params x : 人
  premise P x
  conclude Q x
  source text "测试" locator "R"
"#;

/// `Q 甲` is licensed only by an interpretation and the rule that consumes it
/// must not become a witness (rules never consume interpretation conclusions).
const INTERPRETED: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred S : 人 → Prop
obj 甲 : 人
axiom 事实P : P 甲
  source text "测试" locator "1" version "2020"
interpret 解释Q : P 甲 → Q 甲
  direction expand
  source text "测试" locator "2" version "2020"
rule 规则R :
  params x : 人
  premise P x
  conclude S x
  source text "测试" locator "R"
rule 规则W :
  params x : 人
  premise Q x
  conclude S x
  source text "测试" locator "W"
"#;

/// A pure rule cycle with no assumption or universal fact: nothing can seed
/// the fixed point, so the goal must stay a gap with an explicit loop marker.
const PURE_CYCLE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
obj 甲 : 人
rule 规则S :
  params x : 人
  premise Q x
  conclude P x
  source text "测试" locator "S"
rule 规则R :
  params x : 人
  premise P x
  conclude Q x
  source text "测试" locator "R"
"#;

/// Two-parameter rule; the same instance written with reordered bindings must
/// not count as a second independent witness.
const TWO_PARAM: &str = r#"
sort 人
pred P : 人 → Prop
pred R : 人 → Prop
pred Q : 人 → Prop
obj 甲 : 人
obj 乙 : 人
obj 丙 : 人
axiom 事实P : P 甲
  source text "测试" locator "1"
axiom 事实乙 : R 乙
  source text "测试" locator "2"
axiom 事实丙 : R 丙
  source text "测试" locator "3"
rule 规则 :
  params x : 人
  params y : 人
  premise P x
  premise R y
  conclude Q x
  source text "测试" locator "R"
"#;

/// Conclusion is a function value; the η-variant `谓 (λx. 好人 x)` is kernel
/// equivalent to `谓 好人`.
const ETA: &str = r#"
sort 人
pred 好人 : 人 → Prop
pred 谓 : (人 → Prop) → Prop
obj 甲 : 人
axiom 事实 : 好人 甲
  source text "测试" locator "1"
rule 规则A :
  premise 好人 甲
  conclude 谓 好人
  source text "测试" locator "A"
rule 规则B :
  premise 好人 甲
  conclude 谓 好人
  source text "测试" locator "B"
"#;

/// `objects` distinct `P` facts plus `rules` rules concluding the same `Q`.
fn scale_theory(objects: usize, rules: usize) -> String {
    let mut text = String::from(
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
"#,
    );
    for object in 1..=objects {
        text.push_str(&format!("obj 甲{object:03} : 人\n"));
    }
    for object in 1..=objects {
        text.push_str(&format!(
            "axiom 事实{object:03} : P 甲{object:03}\n  source text \"测试\" locator \"{object:03}\"\n"
        ));
    }
    for rule in 1..=rules {
        text.push_str(&format!(
            "rule 规则{rule:03} :\n  params x : 人\n  premise P x\n  conclude Q x\n  \
             source text \"测试\" locator \"规则{rule:03}\"\n"
        ));
    }
    text
}

fn run(commands: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .args(commands)
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

/// A temporary directory removed when the test ends (including on panic).
struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(tag: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-witness-{}-{tag}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap_or_else(|error| {
            panic!("create {}: {error}", path.display());
        });
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

fn load_and(theory: &Path, commands: &[String]) -> Output {
    load_and_options(&[], theory, commands)
}

fn load_and_options(options: &[&str], theory: &Path, commands: &[String]) -> Output {
    let mut all: Vec<String> = options.iter().map(|arg| arg.to_string()).collect();
    all.push(format!(":load {}", theory.display()));
    all.extend_from_slice(commands);
    run(all)
}

/// The certificate JSON emitted by `:cert`, as text.
fn certificate_text(output: &Output) -> String {
    let text = stdout(output);
    let start = text
        .find('{')
        .unwrap_or_else(|| panic!("no certificate JSON in stdout:\n{text}"));
    text[start..].trim_end().to_owned()
}

fn generated(theory: &Path, goal: &str) -> Certificate {
    let output = load_and(theory, &[format!(":cert {goal}")]);
    assert_exit(&output, PROVED);
    Certificate::from_json(&certificate_text(&output)).expect("the certificate JSON parses")
}

fn write_certificate(dir: &TempDir, tag: &str, certificate: &Certificate) -> PathBuf {
    let json = certificate
        .to_json_pretty()
        .expect("the mutated certificate serializes");
    dir.write(&format!("{tag}.json"), &json)
}

fn verify(dir: &TempDir, theory: &Path, tag: &str, certificate: &Certificate) -> Output {
    verify_with_options(&[], dir, theory, tag, certificate)
}

fn verify_with_options(
    options: &[&str],
    dir: &TempDir,
    theory: &Path,
    tag: &str,
    certificate: &Certificate,
) -> Output {
    let path = write_certificate(dir, tag, certificate);
    load_and_options(
        options,
        theory,
        &[format!(":verify-cert {}", path.display())],
    )
}

/// The index of the witness table entry for the root conclusion.
fn root_group(certificate: &Certificate) -> usize {
    let root = certificate.root.expect("a proved certificate has a root");
    let proposition = match &certificate.nodes[root] {
        Node::RuleApplication { conclusion, .. } | Node::AxiomInstance { conclusion, .. } => {
            conclusion.clone()
        }
        other => panic!("the root is not a derivation step: {other:?}"),
    };
    certificate
        .alternatives
        .iter()
        .position(|group| group.proposition == proposition)
        .unwrap_or_else(|| panic!("the root's conclusion has no witness table entry"))
}

/// Remove one node and renumber every reference that follows it.
fn remove_node(certificate: &mut Certificate, removed: usize) {
    certificate.nodes.remove(removed);
    for node in &mut certificate.nodes {
        match node {
            Node::RuleApplication { premises, .. } => {
                for premise in premises {
                    if *premise > removed {
                        *premise -= 1;
                    }
                }
            }
            Node::InterpretationApplication { premise, .. } if *premise > removed => {
                *premise -= 1;
            }
            Node::InterpretationApplication { .. } => {}
            _ => {}
        }
    }
    if let Some(root) = certificate.root {
        assert_ne!(root, removed, "the test must remove a non-root witness");
        if root > removed {
            certificate.root = Some(root - 1);
        }
    }
    for group in &mut certificate.alternatives {
        group.witnesses.retain(|witness| *witness != removed);
        for witness in &mut group.witnesses {
            if *witness > removed {
                *witness -= 1;
            }
        }
    }
    for obligation in &mut certificate.open_obligations {
        obligation.nodes.retain(|node| *node != removed);
        for node in &mut obligation.nodes {
            if *node > removed {
                *node -= 1;
            }
        }
    }
}

#[test]
fn why_names_the_other_independent_derivation() {
    let dir = TempDir::new("why-two");
    let theory = dir.write("two.std", TWO_RULES);
    let output = load_and(&theory, &[":why Q 甲".to_owned()]);
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    assert!(
        text.contains("另有 1 条独立推导。"),
        "the second derivation must be named:\n{text}"
    );
    // The formal tree still expands one main path: only one rule's conclusion
    // line is printed for the root.
    assert_eq!(
        text.matches("▸ Q 甲  ⟨规则A⟩").count(),
        1,
        "the tree must show one main path:\n{text}"
    );
}

#[test]
fn cert_records_both_witnesses_and_verify_accepts_it() {
    let dir = TempDir::new("cert-two");
    let theory = dir.write("two.std", TWO_RULES);
    let certificate = generated(&theory, "Q 甲");
    assert_eq!(certificate.format_version.get(), 13);
    let group = &certificate.alternatives[root_group(&certificate)];
    assert_eq!(group.witnesses.len(), 2);
    assert!(!group.truncated);
    let rules: Vec<&str> = group
        .witnesses
        .iter()
        .map(|id| match &certificate.nodes[*id] {
            Node::RuleApplication { rule, .. } => rule.as_str(),
            other => panic!("a witness is not a rule step: {other:?}"),
        })
        .collect();
    assert_eq!(rules, ["规则A", "规则B"]);

    let checked = verify(&dir, &theory, "generated", &certificate);
    assert_exit(&checked, PROVED);
    assert!(
        stdout(&checked).contains("逻辑校验：通过"),
        "{}",
        stdout(&checked)
    );
}

#[test]
fn the_certificate_is_byte_identical_across_runs() {
    let dir = TempDir::new("determinism");
    let theory = dir.write("two.std", TWO_RULES);
    let first = load_and(&theory, &[":cert Q 甲".to_owned()]);
    let second = load_and(&theory, &[":cert Q 甲".to_owned()]);
    assert_exit(&first, PROVED);
    assert_exit(&second, PROVED);
    assert_eq!(certificate_text(&first), certificate_text(&second));
}

#[test]
fn removing_one_witness_leaves_the_remaining_derivation_passing() {
    let dir = TempDir::new("remove-one");
    let theory = dir.write("two.std", TWO_RULES);
    let mut certificate = generated(&theory, "Q 甲");
    let root = certificate.root.unwrap();
    let group = root_group(&certificate);
    let other = certificate.alternatives[group]
        .witnesses
        .iter()
        .copied()
        .find(|witness| *witness != root)
        .expect("there is a second witness");
    remove_node(&mut certificate, other);
    assert_eq!(
        certificate.alternatives[group].witnesses.len(),
        1,
        "the remaining witness stays listed"
    );

    let checked = verify(&dir, &theory, "one-left", &certificate);
    assert_exit(&checked, PROVED);
}

#[test]
fn removing_every_witness_fails_the_check() {
    let dir = TempDir::new("remove-all");
    let theory = dir.write("two.std", TWO_RULES);
    let mut certificate = generated(&theory, "Q 甲");
    let group = root_group(&certificate);
    certificate.alternatives[group].witnesses.clear();
    let checked = verify(&dir, &theory, "none-left", &certificate);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains("结论无见证"),
        "the checker must report the missing witness:\n{out}"
    );
}

#[test]
fn a_witness_pointing_at_an_unrelated_premise_is_rejected() {
    let dir = TempDir::new("bad-premise");
    let theory = dir.write("two.std", TWO_RULES);
    let mut certificate = generated(&theory, "Q 甲");
    let root = certificate.root.unwrap();
    let group = root_group(&certificate);
    let other = certificate.alternatives[group]
        .witnesses
        .iter()
        .copied()
        .find(|witness| *witness != root)
        .expect("there is a second witness");
    // Node `root` proves `Q 甲`, not the premise `P 甲` the rule consumes.
    match &mut certificate.nodes[other] {
        Node::RuleApplication { premises, .. } => premises[0] = root,
        other => panic!("the witness is not a rule step: {other:?}"),
    }
    let checked = verify(&dir, &theory, "bad-premise", &certificate);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(out.contains("逻辑校验：失败"), "{out}");
    assert!(
        out.contains("前提实例") || out.contains("证明的是"),
        "the error must name the premise mismatch:\n{out}"
    );
}

#[test]
fn listing_one_node_twice_is_rejected_as_not_independent() {
    let dir = TempDir::new("duplicate-node");
    let theory = dir.write("two.std", TWO_RULES);
    let mut certificate = generated(&theory, "Q 甲");
    let group = root_group(&certificate);
    let witness = certificate.alternatives[group].witnesses[0];
    certificate.alternatives[group].witnesses = vec![witness, witness];
    let checked = verify(&dir, &theory, "duplicate-node", &certificate);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains("重复节点") || out.contains("不独立"),
        "the checker must reject a repeated node:\n{out}"
    );
}

#[test]
fn two_nodes_of_the_same_rule_and_bindings_are_not_independent() {
    let dir = TempDir::new("duplicate-instance");
    let theory = dir.write("two.std", TWO_RULES);
    let mut certificate = generated(&theory, "Q 甲");
    let root = certificate.root.unwrap();
    let group = root_group(&certificate);
    let other = certificate.alternatives[group]
        .witnesses
        .iter()
        .copied()
        .find(|witness| *witness != root)
        .expect("there is a second witness");
    // Make the second node the very same rule instance as the first.
    certificate.nodes[other] = certificate.nodes[root].clone();
    let checked = verify(&dir, &theory, "duplicate-instance", &certificate);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains("不算独立见证"),
        "the checker must reject duplicate rule instances:\n{out}"
    );
}

#[test]
fn the_root_must_be_listed_among_its_own_witnesses() {
    let dir = TempDir::new("root-not-listed");
    let theory = dir.write("two.std", TWO_RULES);
    let mut certificate = generated(&theory, "Q 甲");
    let root = certificate.root.unwrap();
    let group = root_group(&certificate);
    let other = certificate.alternatives[group]
        .witnesses
        .iter()
        .copied()
        .find(|witness| *witness != root)
        .expect("there is a second witness");
    certificate.alternatives[group].witnesses = vec![other];
    let checked = verify(&dir, &theory, "root-not-listed", &certificate);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains("没有列出根节点"),
        "the root consistency check must run:\n{out}"
    );
}

#[test]
fn exceeding_the_bound_is_explicit_and_still_verifies() {
    let dir = TempDir::new("truncated");
    let theory = dir.write("ten.std", &ten_rules());
    let output = load_and(&theory, &[":why Q 甲".to_owned(), ":cert Q 甲".to_owned()]);
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    assert!(text.contains("另有 7 条独立推导。"), "{text}");
    assert!(
        text.contains("该结论的见证已截断：还有更多推导未列出。"),
        "{text}"
    );
    // `:cert` follows `:why` in the same process; take the last JSON object.
    let json_start = text
        .rfind("{\n  \"format_version\"")
        .expect("a certificate");
    let certificate =
        Certificate::from_json(text[json_start..].trim_end()).expect("the certificate JSON parses");
    let group = &certificate.alternatives[root_group(&certificate)];
    assert_eq!(group.witnesses.len(), MAX_CERT_WITNESSES_PER_CONCLUSION);
    assert!(group.truncated);

    let checked = verify(&dir, &theory, "truncated", &certificate);
    assert_exit(&checked, PROVED);
}

#[test]
fn a_conflict_side_names_the_rule_and_the_other_witness() {
    let dir = TempDir::new("conflict");
    let theory = dir.write("conflict.std", CONFLICT);
    let output = load_and(&theory, &[":why 好 甲".to_owned()]);
    assert_exit(&output, GAP);
    let text = stdout(&output);
    assert!(text.contains("冲突未决"), "{text}");
    assert!(
        text.contains("规则 ⟨规则A⟩，另有 1 条规则见证：⟨规则B⟩"),
        "the side with two rules must name both:\n{text}"
    );
    assert!(
        text.contains("左：坏 甲  ← 规则 ⟨规则C⟩") || text.contains("右：坏 甲  ← 规则 ⟨规则C⟩"),
        "the opposite side must name its own rule:\n{text}"
    );

    // The exported certificate records each side's rule witness separately.
    let output = load_and(&theory, &[":cert 好 甲".to_owned()]);
    assert_exit(&output, GAP);
    let certificate = Certificate::from_json(&certificate_text(&output)).expect("valid JSON");
    let mut rules = Vec::new();
    for conflict in &certificate.conflicts {
        for provenance in [&conflict.left_by, &conflict.right_by] {
            if let Provenance::Rules { rules: named } = provenance {
                rules.extend(named.iter().cloned());
            }
        }
    }
    for rule in ["规则A", "规则B", "规则C"] {
        assert!(
            rules.contains(&rule.to_owned()),
            "missing {rule}: {rules:?}"
        );
    }
    let checked = verify(&dir, &theory, "conflict", &certificate);
    assert_exit(&checked, GAP);
    assert!(stdout(&checked).contains("逻辑校验：通过"));
}

#[test]
fn review_reports_the_alternative_count_consistently() {
    let dir = TempDir::new("review");
    let theory = dir.write("two.std", TWO_RULES);
    let output = load_and(&theory, &[":review Q 甲".to_owned()]);
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    assert!(
        text.contains("**独立推导：**已记录 2 条见证（另有 1 条已记录）。"),
        "the review report must repeat the certificate's count:\n{text}"
    );
}

#[test]
fn a_legal_universal_witness_breaks_a_rule_cycle() {
    let dir = TempDir::new("cycle");
    let theory = dir.write("cycle.std", CYCLE);
    let output = load_and(&theory, &[":why Q 甲".to_owned()]);
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    assert!(
        text.contains("〈公理 全称"),
        "the universal instance must appear in the tree:\n{text}"
    );
    assert!(
        text.contains("另有 1 条独立推导。"),
        "both the rule and the universal instance are witnesses:\n{text}"
    );

    let certificate = generated(&theory, "Q 甲");
    let checked = verify(&dir, &theory, "cycle", &certificate);
    assert_exit(&checked, PROVED);
}

#[test]
fn an_interpretation_conclusion_never_becomes_a_rule_witness() {
    let dir = TempDir::new("interpreted");
    let theory = dir.write("interp.std", INTERPRETED);
    let output = load_and_options(
        &["--interpret", "解释Q"],
        &theory,
        &[":why S 甲".to_owned()],
    );
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    assert!(
        !text.contains("⟨规则W⟩"),
        "rule W consumes the interpretation conclusion and must not be a rule step:\n{text}"
    );
    assert!(text.contains("⟨规则R⟩"), "{text}");

    let output = load_and_options(
        &["--interpret", "解释Q"],
        &theory,
        &[":cert S 甲".to_owned()],
    );
    assert_exit(&output, PROVED);
    let certificate = Certificate::from_json(&certificate_text(&output)).expect("valid JSON");
    let group = &certificate.alternatives[root_group(&certificate)];
    assert_eq!(group.witnesses.len(), 1);
    match &certificate.nodes[group.witnesses[0]] {
        Node::RuleApplication { rule, .. } => assert_eq!(rule, "规则R"),
        other => panic!("the witness is not a rule step: {other:?}"),
    }
    let checked = verify_with_options(
        &["--interpret", "解释Q"],
        &dir,
        &theory,
        "interpreted",
        &certificate,
    );
    assert_exit(&checked, PROVED);
}

#[test]
fn a_pure_rule_cycle_is_reported_as_a_gap_with_a_loop_marker() {
    let dir = TempDir::new("pure-cycle");
    let theory = dir.write("cycle.std", PURE_CYCLE);
    let output = load_and(&theory, &[":why Q 甲".to_owned(), ":gap Q 甲".to_owned()]);
    assert_exit(&output, GAP);
    let text = stdout(&output);
    assert!(
        text.contains("证书有效，但根为缺口，结论未被证明。"),
        "the loop must never be presented as a proof:\n{text}"
    );
    assert!(
        text.contains("循环依赖"),
        "the gap must name the rule cycle explicitly:\n{text}"
    );
}

#[test]
fn reordering_the_bindings_of_the_same_instance_does_not_make_it_independent() {
    let dir = TempDir::new("binding-order");
    let theory = dir.write("two-param.std", TWO_PARAM);
    let mut certificate = generated(&theory, "Q 甲");
    let root = certificate.root.unwrap();
    let group = root_group(&certificate);
    let mut clone = certificate.nodes[root].clone();
    match &mut clone {
        Node::RuleApplication { bindings, .. } => bindings.reverse(),
        other => panic!("the root is not a rule step: {other:?}"),
    }
    let clone_id = certificate.nodes.len();
    certificate.nodes.push(clone);
    certificate.alternatives[group].witnesses.push(clone_id);

    let checked = verify(&dir, &theory, "binding-order", &certificate);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains("不算独立见证") || out.contains("同一条规则实例"),
        "reordered bindings must not count as a second witness:\n{out}"
    );
}

#[test]
fn an_eta_variant_cannot_bypass_the_root_witness_check() {
    let dir = TempDir::new("eta");
    let theory = dir.write("eta.std", ETA);
    let mut certificate = generated(&theory, "谓 好人");
    let root = certificate.root.unwrap();
    let group = root_group(&certificate);
    let other = certificate.alternatives[group]
        .witnesses
        .iter()
        .copied()
        .find(|witness| *witness != root)
        .expect("there is a second witness");
    let eta = CertExpr::App {
        func: Box::new(CertExpr::Const {
            name: "谓".to_owned(),
        }),
        arg: Box::new(CertExpr::Lam {
            binder: Some("x".to_owned()),
            domain: Box::new(CertExpr::Const {
                name: "人".to_owned(),
            }),
            body: Box::new(CertExpr::App {
                func: Box::new(CertExpr::Const {
                    name: "好人".to_owned(),
                }),
                arg: Box::new(CertExpr::Var { index: 0 }),
            }),
        }),
    };
    certificate.alternatives[group].proposition = eta;
    certificate.alternatives[group].witnesses = vec![other];

    let checked = verify(&dir, &theory, "eta", &certificate);
    assert_exit(&checked, ERROR);
    let out = stdout(&checked);
    assert!(
        out.contains("没有列出根节点"),
        "the η variant is the root's conclusion and must list the root:\n{out}"
    );
}

#[test]
fn two_hundred_rules_truncate_at_exactly_eight_recorded_witnesses() {
    let dir = TempDir::new("two-hundred");
    let theory = dir.write("many.std", &scale_theory(1, 200));
    let output = load_and(
        &theory,
        &[":why Q 甲001".to_owned(), ":cert Q 甲001".to_owned()],
    );
    assert_exit(&output, PROVED);
    let text = stdout(&output);
    assert!(text.contains("另有 7 条独立推导。"), "{text}");
    assert!(
        text.contains("该结论的见证已截断：还有更多推导未列出。"),
        "{text}"
    );
    let json_start = text
        .rfind("{\n  \"format_version\"")
        .expect("the certificate JSON");
    let certificate = Certificate::from_json(text[json_start..].trim_end()).expect("valid JSON");
    let group = &certificate.alternatives[root_group(&certificate)];
    assert_eq!(group.witnesses.len(), MAX_CERT_WITNESSES_PER_CONCLUSION);
    assert!(group.truncated);
    let checked = verify(&dir, &theory, "two-hundred", &certificate);
    assert_exit(&checked, PROVED);
}

#[test]
fn a_medium_case_stays_fast_enough_to_export() {
    let dir = TempDir::new("scale");
    let theory = dir.write("scale.std", &scale_theory(30, 10));
    let started = Instant::now();
    let output = load_and(&theory, &[":cert Q 甲001".to_owned()]);
    let elapsed = started.elapsed();
    assert_exit(&output, PROVED);
    assert!(
        elapsed < std::time::Duration::from_secs(3),
        "30 objects × 10 rules took {elapsed:?}; the witness index must be linear, not per-conclusion enumeration"
    );
}

#[test]
fn a_case_over_the_node_bound_fails_early_with_an_actionable_message() {
    let dir = TempDir::new("capacity");
    let theory = dir.write("capacity.std", &scale_theory(1300, 8));
    let started = Instant::now();
    let output = load_and(&theory, &[":why Q 甲001".to_owned()]);
    let elapsed = started.elapsed();
    assert_exit(&output, ERROR);
    let text = format!("{}{}", stdout(&output), stderr(&output));
    assert!(
        text.contains("证书节点数量将超过上限"),
        "the node bound must be reported with its cause:\n{text}"
    );
    assert!(
        text.contains("同一结论的多条见证"),
        "the message must explain the multi-witness node growth:\n{text}"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(45),
        "the estimate must stop the case early, not after minutes; took {elapsed:?}"
    );
}
