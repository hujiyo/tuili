//! Interpretation semantics at the reasoner level: explicit enablement, one
//! step after the rule fixed point, no interpretation chain, conflict
//! witnesses, and the certificate conversion of an application node.

use std_deduce_kernel::Expr;
use std_deduce_lang::Library;
use std_deduce_reason::{
    certificate, Node as ReasonNode, Provenance, Reasoner, Resolution, UnresolvedReason,
};

fn load(src: &str) -> Library {
    let mut lib = Library::new();
    lib.load("interpret.std", src)
        .unwrap_or_else(|error| panic!("load: {error}"));
    lib
}

fn atom(name: &str) -> Expr {
    Expr::apps(Expr::constant(name), [Expr::constant("张三")])
}

const BASE: &str = r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
pred S : 人 → Prop
obj 张三 : 人
axiom 事实P : P 张三
  source text "案情" locator "一"
interpret i1 : P 张三 → Q 张三
  direction literal
  source text "解释" locator "一" version "2020"
interpret i2 : Q 张三 → R 张三
  direction analogy
  source text "解释" locator "二" version "2020"
rule 规则S :
  premise Q 张三
  conclude S 张三
  source text "规则" locator "一"
"#;

fn reasoner<'a>(lib: &'a Library, enabled: &[&str]) -> Reasoner<'a> {
    let mut reasoner = Reasoner::new(&lib.env);
    reasoner.assume_ledger_axioms().unwrap();
    for id in enabled {
        reasoner
            .enable_interpretation(id)
            .unwrap_or_else(|error| panic!("enable {id}: {error}"));
    }
    reasoner.saturate().unwrap();
    reasoner
}

#[test]
fn an_interpretation_only_applies_when_enabled() {
    let lib = load(BASE);
    let disabled = reasoner(&lib, &[]);
    assert!(!disabled.knows(&atom("Q")), "the default must be inert");

    let enabled = reasoner(&lib, &["i1"]);
    assert!(enabled.knows(&atom("Q")), "enabling must derive `to`");
    assert_eq!(enabled.enabled_interpretations().len(), 1);

    let derivation = enabled.derivation();
    let root = enabled.root_for(&atom("Q")).expect("`to` has a node");
    let ReasonNode::InterpretationApplication {
        interpretation,
        premise,
        ..
    } = &derivation.nodes[root]
    else {
        panic!("the root must be an interpretation application");
    };
    assert_eq!(interpretation.as_ref(), "i1");
    assert!(matches!(
        derivation.nodes[*premise],
        ReasonNode::Assumption { .. }
    ));
    assert_eq!(derivation.interpretations.len(), 1);
    assert_eq!(derivation.interpretations[0].id.as_ref(), "i1");
}

#[test]
fn an_interpretation_applies_on_a_rule_conclusion() {
    // The base is not just the assumption table: an interpretation whose
    // `from` is a rule conclusion applies after the rule fixed point, one
    // step further. The premise of the application node is that rule step.
    let lib = load(
        r#"
sort 人
pred A : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
obj 张三 : 人
axiom 事实A : A 张三
  source text "案情" locator "一"
rule 规则Q :
  premise A 张三
  conclude Q 张三
  source text "规则" locator "一"
interpret i : Q 张三 → R 张三
  direction literal
  source text "解释" locator "一" version "2020"
"#,
    );
    let reasoner = reasoner(&lib, &["i"]);
    assert!(reasoner.knows(&atom("Q")), "the rule conclusion holds");
    assert!(
        reasoner.knows(&atom("R")),
        "the interpretation must read a rule conclusion"
    );

    let derivation = reasoner.derivation();
    let root = reasoner.root_for(&atom("R")).expect("`to` has a node");
    let ReasonNode::InterpretationApplication { premise, .. } = &derivation.nodes[root] else {
        panic!("the root must be an interpretation application");
    };
    assert!(
        matches!(
            derivation.nodes[*premise],
            ReasonNode::RuleApplication { .. }
        ),
        "the premise must be the rule step that proves `from`"
    );
}

#[test]
fn an_interpretation_step_never_chains_and_never_feeds_a_rule() {
    // i1: P -> Q, i2: Q -> R, ruleS: Q -> S. Even with both interpretations
    // and the rule enabled, only `Q` is licensed: i2 would consume another
    // interpretation's conclusion, and the rule would consume it too.
    let lib = load(BASE);
    let reasoner = reasoner(&lib, &["i1", "i2"]);
    assert!(reasoner.knows(&atom("Q")));
    assert!(!reasoner.knows(&atom("R")), "interpretation chain");
    assert!(!reasoner.knows(&atom("S")), "rule must not consume `to`");
}

#[test]
fn an_interpretation_hint_lists_the_unenabled_declaration() {
    let lib = load(BASE);
    let disabled = reasoner(&lib, &[]);
    let hints = disabled
        .unused_interpretation_hints(&[atom("Q")])
        .expect("conversion is decidable");
    assert_eq!(hints.len(), 1);
    assert_eq!(hints[0].id.as_ref(), "i1");
    assert_eq!(hints[0].from, atom("P"));
    assert_eq!(hints[0].to, atom("Q"));

    // `i2` is not offered while its premise is not established.
    let hints = disabled
        .unused_interpretation_hints(&[atom("R")])
        .expect("conversion is decidable");
    assert!(hints.is_empty(), "{hints:?}");

    let enabled = reasoner(&lib, &["i1"]);
    let hints = enabled
        .unused_interpretation_hints(&[atom("Q")])
        .expect("conversion is decidable");
    assert!(hints.is_empty(), "an enabled interpretation is not a hint");
}

#[test]
fn enabling_checks_existence_duplicates_and_equivalent_conclusions() {
    let lib = load(BASE);
    let mut reasoner = Reasoner::new(&lib.env);
    assert!(reasoner.enable_interpretation("不存在").is_err());
    reasoner.enable_interpretation("i1").unwrap();
    assert!(
        reasoner.enable_interpretation("i1").is_err(),
        "duplicate enable must fail"
    );

    // i2's `to` is R, so it may be enabled with i1; a second interpretation
    // with the same `to` as i1 may not.
    let lib = load(
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
obj 张三 : 人
axiom 事实P : P 张三
  source text "案情" locator "一"
axiom 事实R : R 张三
  source text "案情" locator "二"
interpret i1 : P 张三 → Q 张三
  direction literal
  source text "解释" locator "一" version "2020"
interpret i2 : R 张三 → Q 张三
  direction expand
  source text "解释" locator "二" version "2020"
"#,
    );
    let mut reasoner = Reasoner::new(&lib.env);
    reasoner.enable_interpretation("i1").unwrap();
    let error = reasoner
        .enable_interpretation("i2")
        .expect_err("two kernel-equivalent `to` conclusions must be refused");
    assert!(error.contains("内核下等价"), "{error}");
    assert!(error.contains("disable"), "{error}");
}

#[test]
fn a_conflict_witness_is_the_interpretation_not_a_lost_rule() {
    let lib = load(
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
obj 张三 : 人
contrary Q R
axiom 事实P : P 张三
  source text "案情" locator "一"
rule 规则R :
  conclude R 张三
  source text "规则" locator "一"
interpret i1 : P 张三 → Q 张三
  direction literal
  source text "解释" locator "一" version "2020"
"#,
    );
    let reasoner = reasoner(&lib, &["i1"]);
    assert!(!reasoner.knows(&atom("Q")), "unresolved sides stay out");
    let conflicts = reasoner.conflicts();
    assert_eq!(conflicts.len(), 1);
    let conflict = &conflicts[0];
    assert_eq!(
        conflict.resolution,
        Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority
        }
    );
    let mut provenances = [&conflict.left_by, &conflict.right_by];
    provenances.sort_by_key(|provenance| match provenance {
        Provenance::Rules(_) => 0,
        Provenance::Interpretation(_) => 1,
        Provenance::Assumption => 2,
    });
    assert!(matches!(
        provenances[0],
        Provenance::Rules(rules) if rules.len() == 1 && rules[0].as_ref() == "规则R"
    ));
    assert!(matches!(
        provenances[1],
        Provenance::Interpretation(id) if id.as_ref() == "i1"
    ));

    // The certificate records the interpretation witness even though the
    // interpretation's conclusion node is not in the settled proof graph, and
    // both layers accept it (the root is the fact, not the conflicted `Q`).
    let mut derivation = reasoner.derivation();
    derivation.root = reasoner.root_for(&atom("P"));
    let certificate =
        certificate(&derivation, &reasoner.priority_order()).expect("the derivation converts");
    assert_eq!(certificate.interpretations.len(), 1);
    assert_eq!(certificate.interpretations[0].id, "i1");
    let witness = [
        &certificate.conflicts[0].left_by,
        &certificate.conflicts[0].right_by,
    ]
    .into_iter()
    .find_map(|provenance| match provenance {
        std_deduce_cert::Provenance::Interpretation { interpretation } => Some(*interpretation),
        _ => None,
    })
    .expect("one side records the interpretation witness");
    assert_eq!(witness, 0, "the witness is an index into the table");
    let report = std_deduce_cert::check(&lib.env, &certificate)
        .expect("the interpretation conflict is well-formed");
    assert!(report.root_proved);
    std_deduce_cert::kernel_proof(&lib.env, &certificate).expect("the kernel proof passes");
}

#[test]
fn an_interpretation_application_certificate_checks_and_proves() {
    let lib = load(BASE);
    let reasoner = reasoner(&lib, &["i1"]);
    let mut derivation = reasoner.derivation();
    derivation.root = reasoner.root_for(&atom("Q"));
    let certificate =
        certificate(&derivation, &reasoner.priority_order()).expect("the derivation converts");

    assert_eq!(certificate.interpretations.len(), 1);
    assert_eq!(
        certificate.interpretations[0].direction,
        std_deduce_cert::InterpretationDirection::Literal
    );
    let root = certificate.root.expect("the root is recorded");
    let std_deduce_cert::Node::InterpretationApplication {
        interpretation,
        premise,
        ..
    } = &certificate.nodes[root]
    else {
        panic!("the root is an interpretation application");
    };
    assert_eq!(*interpretation, 0);
    assert_eq!(*premise, 0);

    let report = std_deduce_cert::check(&lib.env, &certificate).expect("the certificate checks");
    assert!(report.root_proved);
    let kernel = std_deduce_cert::kernel_proof(&lib.env, &certificate).expect("the proof passes");
    assert!(kernel.root_proved);
}
