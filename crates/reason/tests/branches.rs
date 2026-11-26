//! The candidate-interpretation scan for an open-concept-obstructed outcome.
//!
//! These tests pin the criterion the `:branches` command reports on: only the
//! interpretation's `to` is compared, exact (kernel-equivalent) and same-head
//! candidates are distinguished, an interpretation whose `from` does not hold
//! is reported as unavailable, a direction-reversed one is not a candidate,
//! and the bound names what it leaves out.

use std_deduce_kernel::Expr;
use std_deduce_lang::Library;
use std_deduce_reason::{CandidateRelation, Reasoner, MAX_BRANCH_CANDIDATES};

fn load(src: &str) -> Library {
    let mut lib = Library::new();
    lib.load("branches.std", src)
        .unwrap_or_else(|error| panic!("load: {error}"));
    lib
}

fn atom(name: &str, argument: &str) -> Expr {
    Expr::apps(Expr::constant(name), [Expr::constant(argument)])
}

fn reasoner<'a>(lib: &'a Library, enabled: &[&str]) -> Reasoner<'a> {
    let mut reasoner = Reasoner::new(&lib.env);
    reasoner.assume_ledger_axioms().unwrap();
    for id in enabled {
        reasoner.enable_interpretation(id).unwrap();
    }
    reasoner.saturate().unwrap();
    reasoner
}

const CRITERION_CASE: &str = r#"
sort 人
pred 情节严重 : 人 → Prop
pred 其他 : 人 → Prop
pred 成立 : 人 → Prop
pred 未成立 : 人 → Prop
obj 张三 : 人
obj 李四 : 人
open 情节严重
axiom 成立张三 : 成立 张三
  source text "案情" locator "一"
axiom 成立李四 : 成立 李四
  source text "案情" locator "二"
interpret iExact : 成立 张三 → 情节严重 张三
  direction literal
  source text "解释" locator "一" version "2020"
interpret iOther : 成立 李四 → 情节严重 李四
  direction literal
  source text "解释" locator "二" version "2020"
interpret iUnrelated : 成立 张三 → 其他 张三
  direction literal
  source text "解释" locator "三" version "2020"
interpret iReverse : 情节严重 张三 → 其他 张三
  direction literal
  source text "解释" locator "四" version "2020"
interpret iNoFrom : 未成立 张三 → 情节严重 张三
  direction literal
  source text "解释" locator "五" version "2020"
"#;

#[test]
fn exact_and_same_head_candidates_are_distinguished_and_reversed_or_unrelated_ones_vanish() {
    let lib = load(CRITERION_CASE);
    let reasoner = reasoner(&lib, &[]);
    let blocked = atom("情节严重", "张三");

    // The same blocked proposition passed twice must still be one entry.
    let scan = reasoner
        .branch_candidates(&[blocked.clone(), blocked.clone()])
        .expect("candidate scan");
    assert_eq!(scan.blocked, vec![blocked.clone()], "deduplicated by key");

    let ids: Vec<&str> = scan.candidates.iter().map(|c| c.id.as_ref()).collect();
    assert_eq!(ids, ["iExact", "iOther"], "sorted by id");
    assert_eq!(scan.candidates[0].relation, CandidateRelation::Exact);
    assert_eq!(scan.candidates[1].relation, CandidateRelation::SameHead);
    assert_eq!(
        scan.candidates[0].blocked, blocked,
        "a candidate names the blocked proposition it relates to"
    );

    assert_eq!(scan.unavailable.len(), 1);
    assert_eq!(scan.unavailable[0].candidate.id.as_ref(), "iNoFrom");
    assert!(
        scan.unavailable[0]
            .reason
            .contains("from 在解释应用前的事实集"),
        "the reason must say which fact set was read: {}",
        scan.unavailable[0].reason
    );

    for absent in ["iUnrelated", "iReverse"] {
        assert!(
            !scan
                .candidates
                .iter()
                .any(|candidate| candidate.id.as_ref() == absent),
            "{absent} must not be a candidate"
        );
        assert!(
            !scan
                .unavailable
                .iter()
                .any(|entry| entry.candidate.id.as_ref() == absent),
            "{absent} must not be listed as unavailable either"
        );
    }
}

#[test]
fn a_gap_tree_names_the_open_concepts_it_is_blocked_on() {
    let lib = load(CRITERION_CASE);
    let reasoner = reasoner(&lib, &[]);
    let goal = atom("情节严重", "张三");
    let tree = reasoner.gap_tree(&goal).expect("gap tree");
    let blocked = reasoner.open_concept_goals(&tree).expect("open goals");
    assert_eq!(blocked, vec![goal]);
}

fn cap_case(count: usize) -> String {
    let mut theory = String::from(
        "sort 人\npred 情节严重 : 人 → Prop\nobj 张三 : 人\nopen 情节严重\n\
         axiom 成立 : 情节严重 张三\n  source text \"案情\" locator \"一\"\n",
    );
    for index in 0..count {
        theory.push_str(&format!(
            "interpret i{} : 情节严重 张三 → 情节严重 张三\n  direction literal\n  \
             source text \"解释\" locator \"{}\" version \"2020\"\n",
            (b'A' + index as u8) as char,
            index
        ));
    }
    theory
}

#[test]
fn the_bound_keeps_the_first_ids_and_names_the_omitted_ones() {
    let lib = load(&cap_case(10));
    let reasoner = reasoner(&lib, &[]);
    let scan = reasoner
        .branch_candidates(&[atom("情节严重", "张三")])
        .expect("candidate scan");
    assert_eq!(scan.candidates.len(), MAX_BRANCH_CANDIDATES);
    assert_eq!(
        scan.truncated.len(),
        2,
        "the two candidates past the bound are named"
    );
    assert_eq!(scan.truncated[0].as_ref(), "iI");
    assert_eq!(scan.truncated[1].as_ref(), "iJ");
}

#[test]
fn an_enabled_interpretation_is_baseline_and_an_equivalent_to_is_unavailable() {
    let theory = format!(
        "{CRITERION_CASE}interpret iSameTo : 成立 李四 → 情节严重 张三\n  direction literal\n  \
         source text \"解释\" locator \"六\" version \"2020\"\n"
    );
    let lib = load(&theory);
    let reasoner = reasoner(&lib, &["iExact"]);
    let scan = reasoner
        .branch_candidates(&[atom("情节严重", "张三")])
        .expect("candidate scan");
    assert!(
        !scan
            .candidates
            .iter()
            .any(|candidate| candidate.id.as_ref() == "iExact"),
        "an already enabled interpretation belongs to the baseline"
    );
    let unavailable: Vec<&str> = scan
        .unavailable
        .iter()
        .map(|entry| entry.candidate.id.as_ref())
        .collect();
    assert!(unavailable.contains(&"iSameTo"), "{unavailable:?}");
    let entry = scan
        .unavailable
        .iter()
        .find(|entry| entry.candidate.id.as_ref() == "iSameTo")
        .expect("iSameTo");
    assert!(
        entry.reason.contains("iExact"),
        "the collision names the enabled declaration: {}",
        entry.reason
    );
}

#[test]
fn a_reasoner_without_a_settled_fact_base_is_an_error_not_an_empty_scan() {
    let lib = load(CRITERION_CASE);
    let reasoner = Reasoner::new(&lib.env);
    let error = reasoner
        .branch_candidates(&[atom("情节严重", "张三")])
        .expect_err("an unsaturated reasoner cannot judge availability");
    assert!(
        error.contains("饱和"),
        "the error must name the missing saturation: {error}"
    );
}

/// The relation is decided over the whole blocked set: a same-head proposition
/// that sorts before the kernel-equivalent one must not hide the exact match.
#[test]
fn exact_match_wins_even_when_a_same_head_proposition_sorts_first() {
    let lib = load(
        r#"
sort 人
pred 情节严重 : 人 → Prop
pred 触发 : 人 → Prop
obj 丙 : 人
obj 乙 : 人
open 情节严重
axiom 触发丙 : 触发 丙
  source text "案情" locator "一"
axiom 触发乙 : 触发 乙
  source text "案情" locator "二"
interpret iOther : 触发 丙 → 情节严重 丙
  direction literal
  source text "解释" locator "一" version "2020"
interpret iExact : 触发 乙 → 情节严重 乙
  direction literal
  source text "解释" locator "二" version "2020"
"#,
    );
    let reasoner = reasoner(&lib, &[]);
    let exact = atom("情节严重", "乙");
    let same_head = atom("情节严重", "丙");
    // `丙` sorts before `乙` by the structural key, so the blocked list is
    // [情节严重 丙, 情节严重 乙] — the same-head proposition comes first.
    let scan = reasoner
        .branch_candidates(&[exact.clone(), same_head.clone()])
        .expect("candidate scan");
    let candidate = scan
        .candidates
        .iter()
        .find(|candidate| candidate.id.as_ref() == "iExact")
        .expect("iExact is related");
    assert_eq!(
        candidate.relation,
        CandidateRelation::Exact,
        "a kernel-equivalent to must not be downgraded to same-head"
    );
    assert_eq!(
        candidate.blocked, exact,
        "the exact candidate names the proposition it licenses"
    );
}
