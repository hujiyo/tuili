//! Interpretation semantics at the reasoner level: explicit enablement, one
//! step after the rule fixed point, no interpretation chain, conflict
//! witnesses, and the certificate conversion of an application node.

use std_deduce_kernel::Expr;
use std_deduce_lang::Library;
use std_deduce_reason::{
    certificate, GapStatus, Node as ReasonNode, Provenance, Reasoner, Resolution, UnresolvedReason,
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
fn gap_candidates_judge_premises_against_the_rule_stage() {
    // An enabled interpretation licenses `Q`, but the rule stage never
    // consumes it. `:gap S` must therefore still report `Q` as missing (and
    // `:gap T` must not claim the rule has everything it needs).
    let lib = load(
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred Z : 人 → Prop
pred S : 人 → Prop
pred T : 人 → Prop
obj 张三 : 人
axiom 事实P : P 张三
  source text "案情" locator "一"
interpret i : P 张三 → Q 张三
  direction literal
  source text "解释" locator "一" version "2020"
rule 规则S :
  premise Q 张三
  premise Z 张三
  conclude S 张三
  source text "规则" locator "一"
rule 规则T :
  premise Q 张三
  conclude T 张三
  source text "规则" locator "二"
"#,
    );
    let reasoner = reasoner(&lib, &["i"]);
    assert!(reasoner.knows(&atom("Q")), "the interpretation proves `to`");

    let s = reasoner.explain(&atom("S")).unwrap();
    assert_eq!(s.candidates.len(), 1, "{s:?}");
    assert_eq!(
        s.candidates[0].missing,
        vec![atom("Q"), atom("Z")],
        "`Q` is an interpretation conclusion, not a rule-stage fact"
    );

    let t = reasoner.explain(&atom("T")).unwrap();
    assert_eq!(t.candidates.len(), 1, "{t:?}");
    assert_eq!(
        t.candidates[0].missing,
        vec![atom("Q")],
        "the rule remains blocked by its interpretation-only premise"
    );

    // The child node under the missing premise must not claim the premise is
    // satisfied: it is proved by an interpretation, which no rule may consume.
    let tree = reasoner.gap_tree(&atom("S")).unwrap();
    assert_eq!(tree.candidates.len(), 1, "{tree:?}");
    let q = tree.candidates[0].missing[0]
        .gap
        .as_ref()
        .expect("`Q` expands as a premise");
    assert_eq!(q.status, GapStatus::InterpretedOnly);
}

#[test]
fn hints_cover_only_the_root_goal_and_the_pre_application_facts() {
    // i1 is enabled; i2 consumes i1's conclusion. Enabling i2 would not help
    // (that is an interpretation chain), so `R` must not be hinted.
    let lib = load(
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
obj 张三 : 人
axiom 事实P : P 张三
  source text "案情" locator "一"
interpret i1 : P 张三 → Q 张三
  direction literal
  source text "解释" locator "一" version "2020"
interpret i2 : Q 张三 → R 张三
  direction analogy
  source text "解释" locator "二" version "2020"
"#,
    );
    let chained = reasoner(&lib, &["i1"]);
    assert!(chained.knows(&atom("Q")));
    let hints = chained
        .unused_interpretation_hints(&atom("R"))
        .expect("conversion is decidable");
    assert!(
        hints.is_empty(),
        "an unenabled interpretation whose `from` only holds after another \
         application is a dead end: {hints:?}"
    );

    // The root-only rule: `i2` licenses `R`, and `R` is a premise of a rule
    // for `S`; `S` itself is not made provable by enabling `i2`.
    let lib = load(
        r#"
sort 人
pred P : 人 → Prop
pred Q : 人 → Prop
pred R : 人 → Prop
pred S : 人 → Prop
obj 张三 : 人
axiom 事实P : P 张三
  source text "案情" locator "一"
interpret i : P 张三 → R 张三
  direction literal
  source text "解释" locator "一" version "2020"
rule 规则S :
  premise R 张三
  conclude S 张三
  source text "规则" locator "一"
"#,
    );
    let reasoner = reasoner(&lib, &[]);
    let hints = reasoner
        .unused_interpretation_hints(&atom("R"))
        .expect("conversion is decidable");
    assert_eq!(hints.len(), 1, "the root goal is hinted");
    assert_eq!(hints[0].id.as_ref(), "i");
    let hints = reasoner
        .unused_interpretation_hints(&atom("S"))
        .expect("conversion is decidable");
    assert!(
        hints.is_empty(),
        "a missing rule premise is not hinted: rules do not consume \
         interpretation conclusions: {hints:?}"
    );
}

#[test]
fn a_convertible_to_does_not_produce_a_second_application_step() {
    // The assumption and the interpretation's `to` are alpha variants of the
    // same quantified proposition. The structural key differs, but the kernel
    // says they are the same proposition, so no second step is licensed.
    let lib = load(
        r#"
sort 人
pred P : 人 → Prop
obj 张三 : 人
axiom 全称 : ∀ (x : 人), P x → P x
  source text "案情" locator "一"
axiom 事实P : P 张三
  source text "案情" locator "二"
interpret i : P 张三 → ∀ (y : 人), P y → P y
  direction literal
  source text "解释" locator "一" version "2020"
"#,
    );
    let reasoner = reasoner(&lib, &["i"]);
    let derivation = reasoner.derivation();
    let applications = derivation
        .nodes
        .iter()
        .filter(|node| matches!(node, ReasonNode::InterpretationApplication { .. }))
        .count();
    assert_eq!(
        applications, 0,
        "a kernel-convertible `to` already holds; a second step is redundant"
    );
    assert_eq!(derivation.interpretations.len(), 1);
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
        .unused_interpretation_hints(&atom("Q"))
        .expect("conversion is decidable");
    assert_eq!(hints.len(), 1);
    assert_eq!(hints[0].id.as_ref(), "i1");
    assert_eq!(hints[0].from, atom("P"));
    assert_eq!(hints[0].to, atom("Q"));

    // `i2` is not offered while its premise is not established.
    let hints = disabled
        .unused_interpretation_hints(&atom("R"))
        .expect("conversion is decidable");
    assert!(hints.is_empty(), "{hints:?}");

    let enabled = reasoner(&lib, &["i1"]);
    let hints = enabled
        .unused_interpretation_hints(&atom("Q"))
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
        Provenance::Axiom(_) => 3,
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
    let certificate = certificate(&lib.env, &derivation, &reasoner.priority_order())
        .expect("the derivation converts");
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
    let certificate = certificate(&lib.env, &derivation, &reasoner.priority_order())
        .expect("the derivation converts");

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

/// A conflicted conclusion that only a chain could reach must not be rebuilt by
/// chaining: the conflict side is reconstructed from the rule-visible facts,
/// where an interpretation's own output never appears. The side is then simply
/// unrebuildable, which is reported as such instead of producing a certificate
/// that its own checker rejects.
#[test]
fn a_conflict_side_is_not_rebuilt_by_an_interpretation_chain() {
    let lib = load(
        r#"
sort 人
pred F : 人 → Prop
pred Q : 人 → Prop
pred Z : 人 → Prop
pred R : 人 → Prop
obj 张三 : 人
contrary Z R
axiom 事实F : F 张三
  source text "案情" locator "一"
rule 规则R :
  conclude R 张三
  source text "规则" locator "一"
interpret i1 : F 张三 → Q 张三
  direction literal
  source text "解释" locator "一" version "2020"
interpret i2 : Q 张三 → Z 张三
  direction literal
  source text "解释" locator "二" version "2020"
"#,
    );
    let reasoner = reasoner(&lib, &["i1", "i2"]);
    // `Q` comes from `i1`; `i2` may not read it, so `Z` is never derived.
    assert!(reasoner.knows(&atom("Q")));
    assert!(!reasoner.knows(&atom("Z")), "interpretation chain");
    // The conflict side of `Z` therefore cannot be rebuilt either: the rebuild
    // reads the rule-visible facts, where `Q` never appears, so no witness is
    // produced. The conflict is reported as unrebuildable instead of yielding a
    // certificate that contains an interpretation chain and fails its own
    // checker.
    assert!(
        reasoner.derivation_for(&atom("Z")).is_none(),
        "the conflict side must not be rebuilt by an interpretation chain"
    );
}
