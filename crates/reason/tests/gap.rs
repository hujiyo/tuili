//! Recursive gap trees and the issue scan.
//!
//! These pin down the M3-3 contract: a gap is expanded until the missing
//! premises reach facts or rules that cannot be applied, every recursion is
//! bounded by explicit limits (and says so when a limit stops it), repeated
//! expansions are recognised by a structural key rather than printed text, and
//! `issues` reports every conclusion the current fact set can contest instead
//! of one goal.

use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{name, Expr};
use std_deduce_lang::Library;
use std_deduce_reason::{GapLimit, GapLimits, GapStatus, Reasoner};

fn load(src: &str) -> Library {
    let mut lib = Library::new();
    lib.load("test", src)
        .unwrap_or_else(|e| panic!("load: {e}"));
    lib
}

fn reasoner(lib: &Library) -> Reasoner<'_> {
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    r
}

fn p(name: &str) -> Expr {
    Expr::constant(name)
}

fn goal(name: &str, arg: &str) -> Expr {
    Expr::apps(p(name), [p(arg)])
}

/// A two-step theory: `结论` needs `前提一` and `前提二`; `前提一` itself needs
/// `基础`; `前提二` has no rule at all.
const CHAIN: &str = r#"
sort 人
pred 基础 : 人 → Prop
pred 前提一 : 人 → Prop
pred 前提二 : 人 → Prop
pred 结论 : 人 → Prop
obj 张三 : 人

rule 结论规则 :
  params p : 人
  premise 前提一 p
  premise 前提二 p
  conclude 结论 p
  source text "测试" locator "结论规则"

rule 前提一规则 :
  params p : 人
  premise 基础 p
  conclude 前提一 p
  source text "测试" locator "前提一规则"
"#;

#[test]
fn a_gap_tree_expands_missing_premises_down_to_the_leaves() {
    let lib = load(CHAIN);
    let r = reasoner(&lib);
    let tree = r.gap_tree(&goal("结论", "张三")).unwrap();

    assert_eq!(tree.status, GapStatus::Unreachable);
    assert!(tree.limit.is_none(), "nothing was truncated here");
    assert_eq!(tree.candidates.len(), 1);
    let candidate = &tree.candidates[0];
    assert_eq!(candidate.rule.as_ref(), "结论规则");
    assert_eq!(
        candidate
            .missing
            .iter()
            .map(|missing| print_expr(&missing.premise))
            .collect::<Vec<_>>(),
        ["前提一 张三", "前提二 张三"],
        "missing premises keep the rule's premise order"
    );
    for missing in &candidate.missing {
        assert!(missing.gap.is_some(), "each missing premise is expanded");
    }

    // 前提一 张三 still has a candidate rule; its own missing premise is a leaf.
    let first = candidate.missing[0].gap.as_ref().unwrap();
    assert_eq!(first.status, GapStatus::Unreachable);
    assert_eq!(first.candidates.len(), 1);
    assert_eq!(first.candidates[0].rule.as_ref(), "前提一规则");
    assert_eq!(
        print_expr(&first.candidates[0].missing[0].premise),
        "基础 张三"
    );
    let leaf = first.candidates[0].missing[0].gap.as_ref().unwrap();
    assert_eq!(leaf.status, GapStatus::Unreachable);
    assert!(
        leaf.candidates.is_empty(),
        "no rule concludes 基础, so this is a fact leaf"
    );

    // 前提二 张三 is a leaf too: no rule concludes it.
    let second = candidate.missing[1].gap.as_ref().unwrap();
    assert!(second.candidates.is_empty());
}

#[test]
fn a_rule_cycle_is_cut_by_the_structural_path_key() {
    let src = r#"
sort 人
pred 甲 : 人 → Prop
pred 乙 : 人 → Prop
obj 张三 : 人

rule 甲规则 :
  params p : 人
  premise 乙 p
  conclude 甲 p
  source text "测试" locator "甲规则"

rule 乙规则 :
  params p : 人
  premise 甲 p
  conclude 乙 p
  source text "测试" locator "乙规则"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let tree = r.gap_tree(&goal("甲", "张三")).unwrap();

    let second = tree.candidates[0].missing[0].gap.as_ref().unwrap();
    assert_eq!(second.status, GapStatus::Unreachable);
    let third = second.candidates[0].missing[0].gap.as_ref().unwrap();
    assert_eq!(
        third.status,
        GapStatus::Cycle,
        "甲 is already being expanded on this path"
    );
    assert!(third.candidates.is_empty());
}

#[test]
fn a_premise_with_an_unbound_rule_parameter_is_not_expanded() {
    let src = r#"
sort 人
pred 甲 : 人 → Prop
pred 乙 : 人 → Prop
pred 丙 : 人 → Prop
obj 张三 : 人

rule 规则 :
  params x : 人, y : 人
  premise 甲 x
  premise 乙 y
  conclude 丙 x
  source text "测试" locator "规则"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let tree = r.gap_tree(&goal("丙", "张三")).unwrap();

    let candidate = &tree.candidates[0];
    assert_eq!(
        print_expr(&candidate.missing[1].premise),
        "乙 ?y",
        "the goal determines x but not y"
    );
    let second = candidate.missing[1].gap.as_ref().unwrap();
    assert_eq!(
        second.status,
        GapStatus::OpenPattern,
        "an open pattern is reported as such, not as a proposition"
    );
    assert!(second.candidates.is_empty());
}

#[test]
fn the_depth_limit_stops_the_expansion_and_says_so() {
    let lib = load(CHAIN);
    let r = reasoner(&lib);
    let limits = GapLimits {
        max_depth: 1,
        ..GapLimits::default()
    };
    let tree = r.gap_tree_with(&goal("结论", "张三"), &limits).unwrap();

    assert!(tree.limit.is_none(), "the root is within the depth limit");
    let child = tree.candidates[0].missing[0].gap.as_ref().unwrap();
    assert_eq!(
        child.limit,
        Some(GapLimit::Depth { limit: 1 }),
        "the node at the depth limit reports the truncation"
    );
    assert_eq!(child.candidates.len(), 1);
    assert!(
        child.candidates[0].missing[0].gap.is_none(),
        "no deeper node is built past the depth limit"
    );
}

#[test]
fn the_node_limit_stops_the_expansion_and_says_so() {
    let lib = load(CHAIN);
    let r = reasoner(&lib);
    let limits = GapLimits {
        max_nodes: 2,
        ..GapLimits::default()
    };
    let tree = r.gap_tree_with(&goal("结论", "张三"), &limits).unwrap();

    assert_eq!(tree.limit, Some(GapLimit::Nodes { limit: 2 }));
    let first = tree.candidates[0].missing[0].gap.as_ref().unwrap();
    assert_eq!(first.limit, Some(GapLimit::Nodes { limit: 2 }));
    assert!(
        tree.candidates[0].missing[1].gap.is_none(),
        "the node budget is spent, so the second premise is not expanded"
    );
}

#[test]
fn the_rule_attempt_limit_stops_repeated_expansion_of_one_rule() {
    let src = r#"
sort 人
pred 基础 : 人 → Prop
pred 甲 : 人 → Prop
pred 结论 : 人 → Prop
obj 张三 : 人

rule 根规则 :
  params p : 人
  premise 甲 p
  premise 甲 p
  conclude 结论 p
  source text "测试" locator "根规则"

rule 甲规则 :
  params p : 人
  premise 基础 p
  conclude 甲 p
  source text "测试" locator "甲规则"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let limits = GapLimits {
        max_rule_attempts: 1,
        ..GapLimits::default()
    };
    let tree = r.gap_tree_with(&goal("结论", "张三"), &limits).unwrap();

    let candidate = &tree.candidates[0];
    let first = candidate.missing[0].gap.as_ref().unwrap();
    assert_eq!(first.candidates[0].rule.as_ref(), "甲规则");
    assert!(first.candidates[0].missing[0].gap.is_some());

    let second = candidate.missing[1].gap.as_ref().unwrap();
    assert_eq!(
        second.candidates[0].limit,
        Some(GapLimit::RuleAttempts {
            rule: std_deduce_kernel::name("甲规则"),
            limit: 1,
        }),
        "the second attempt to expand 甲规则 is refused, not silently dropped"
    );
    assert!(second.candidates[0].missing[0].gap.is_none());
}

#[test]
fn issues_list_every_contestable_conclusion_with_its_gap() {
    let src = r#"
sort 人
pred 健在 : 人 → Prop
pred 有住所 : 人 → Prop
pred 失踪 : 人 → Prop
obj 甲 : 人
obj 乙 : 人

axiom 甲健在 : 健在 甲
  source text "测试" locator "甲健在"
axiom 甲有住所 : 有住所 甲
  source text "测试" locator "甲有住所"

rule 宣告失踪 :
  params p : 人
  premise 健在 p
  premise 有住所 p
  conclude 失踪 p
  source text "民法典" locator "第四十条"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let scan = r.issues().unwrap();

    // 失踪 甲 is proved, so only 失踪 乙 can still be argued.
    assert_eq!(scan.issues.len(), 1);
    assert!(scan.limits.is_empty(), "nothing was truncated: {scan:?}");
    let issue = &scan.issues[0];
    assert_eq!(print_expr(&issue.goal), "失踪 乙");
    assert_eq!(issue.status, GapStatus::Unreachable);
    assert_eq!(issue.candidates.len(), 1);
    assert_eq!(issue.candidates[0].rule.as_ref(), "宣告失踪");
    assert_eq!(
        issue.candidates[0]
            .missing
            .iter()
            .map(|missing| print_expr(&missing.premise))
            .collect::<Vec<_>>(),
        ["健在 乙", "有住所 乙"],
        "premises keep the rule's order"
    );
    for missing in &issue.candidates[0].missing {
        assert!(
            missing.gap.is_some(),
            "each issue premise is expanded into its own gap"
        );
    }
}

#[test]
fn issues_sorts_candidates_and_truncates_at_the_issue_limit() {
    let src = r#"
sort 人
pred 健在 : 人 → Prop
pred 有住所 : 人 → Prop
pred 失踪 : 人 → Prop
obj 甲 : 人
obj 乙 : 人
obj 丙 : 人

rule 乙规则 :
  params p : 人
  premise 健在 p
  conclude 失踪 p
  source text "测试" locator "乙规则"

rule 甲规则 :
  params p : 人
  premise 有住所 p
  conclude 失踪 p
  source text "测试" locator "甲规则"
"#;
    let lib = load(src);
    let r = reasoner(&lib);

    let scan = r.issues().unwrap();
    assert_eq!(scan.issues.len(), 3, "one issue per named person");
    let candidates = &scan.issues[0].candidates;
    assert_eq!(candidates.len(), 2, "both rules can conclude the goal");
    let names: Vec<&str> = candidates.iter().map(|c| c.rule.as_ref()).collect();
    let mut sorted = names.clone();
    sorted.sort_unstable();
    assert_eq!(names, sorted, "candidate rules are sorted by name");

    let limits = GapLimits {
        max_issues: 2,
        ..GapLimits::default()
    };
    let scan = r.issues_with(&limits).unwrap();
    assert_eq!(scan.issues.len(), 2, "the issue list stops at the cap");
    assert!(
        scan.limits.contains(&GapLimit::Issues { limit: 2 }),
        "the truncation is reported: {:?}",
        scan.limits
    );
}

#[test]
fn issues_include_the_sides_of_an_unresolved_conflict() {
    let src = r#"
sort 人
pred 申请 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
obj 张三 : 人
contrary 批准 不批准

axiom 张三申请 : 申请 张三
  source text "测试" locator "申请"

rule 准 :
  params p : 人
  premise 申请 p
  conclude 批准 p
  source text "测试" locator "准"

rule 不准 :
  params p : 人
  premise 申请 p
  conclude 不批准 p
  source text "测试" locator "不准"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    assert!(
        !r.knows(&goal("批准", "张三")),
        "an unresolved conflict keeps both sides out of the fact base"
    );
    let scan = r.issues().unwrap();
    let goals: Vec<String> = scan
        .issues
        .iter()
        .map(|issue| print_expr(&issue.goal))
        .collect();
    assert!(
        goals.contains(&"批准 张三".to_owned()) && goals.contains(&"不批准 张三".to_owned()),
        "both conflicted conclusions are contestable: {goals:?}"
    );
    for issue in &scan.issues {
        assert_eq!(
            issue.status,
            GapStatus::Conflicted,
            "a contested conclusion says why it is not asserted"
        );
    }
}

#[test]
fn a_decided_conflict_is_not_an_open_issue() {
    let src = r#"
sort 人
pred 申请 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
obj 张三 : 人
contrary 批准 不批准

axiom 张三申请 : 申请 张三
  source text "测试" locator "申请"

rule 准 :
  params p : 人
  premise 申请 p
  conclude 批准 p
  defeated_by 不准
  source text "测试" locator "准"

rule 不准 :
  params p : 人
  premise 申请 p
  conclude 不批准 p
  source text "测试" locator "不准"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let rejected = goal("批准", "张三");
    let upheld = goal("不批准", "张三");
    assert!(r.knows(&upheld), "the declared priority makes 不批准 win");
    assert!(
        !r.knows(&rejected),
        "the losing side stays out of the fact base"
    );
    assert_eq!(
        r.gap_tree(&rejected).unwrap().status,
        GapStatus::Defeated,
        "a decided loser is no longer an unresolved conflict"
    );
    assert_eq!(r.gap_tree(&upheld).unwrap().status, GapStatus::Proved);
    assert!(
        r.explain(&rejected)
            .unwrap()
            .note
            .as_deref()
            .is_some_and(|note| note.contains("已裁决")),
        "the one-level note must say the conflict was decided, not left open"
    );

    let scan = r.issues().unwrap();
    assert!(
        scan.issues.is_empty(),
        "a decided conflict is not an open issue: {:?}",
        scan.issues
    );
}

#[test]
fn the_root_respects_the_node_limit() {
    let lib = load(CHAIN);
    let r = reasoner(&lib);
    let limits = GapLimits {
        max_nodes: 0,
        ..GapLimits::default()
    };
    let tree = r.gap_tree_with(&goal("结论", "张三"), &limits).unwrap();
    assert_eq!(
        tree.limit,
        Some(GapLimit::Nodes { limit: 0 }),
        "the root itself counts as a node"
    );
    assert!(
        tree.candidates.is_empty(),
        "a root the node budget refuses lists no candidate"
    );
}

#[test]
fn a_definition_alias_matches_like_its_definition() {
    let src = r#"
sort 人
pred 原 : 人 → Prop
pred 结论 : 人 → Prop
obj 张三 : 人
def 结论别名 : 人 → Prop := 结论

rule 规则 :
  params p : 人
  premise 原 p
  conclude 结论 p
  source text "测试" locator "规则"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let aliased = Expr::app(p("结论别名"), p("张三"));
    assert!(
        !r.explain(&aliased).unwrap().candidates.is_empty(),
        "a def alias of the goal's head must find the rule that concludes its definition"
    );
    let tree = r.gap_tree(&aliased).unwrap();
    assert_eq!(tree.candidates.len(), 1);
    assert_eq!(tree.candidates[0].rule.as_ref(), "规则");
    assert_eq!(
        print_expr(&tree.candidates[0].missing[0].premise),
        "原 张三"
    );
}

#[test]
fn issues_report_rules_that_cannot_be_instantiated() {
    let src = r#"
sort 人
sort 物
pred 前提 : 人 → Prop
pred 结论 : 物 → Prop
obj 甲物 : 物

rule 规则 :
  params p : 人
  premise 前提 p
  conclude 结论 甲物
  source text "测试" locator "规则"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let scan = r.issues().unwrap();
    assert!(
        scan.issues.is_empty(),
        "no constant inhabits 人, so no conclusion can be instantiated"
    );
    assert_eq!(
        scan.uninstantiable,
        vec![name("规则")],
        "the rule is reported instead of being silently dropped"
    );
}

#[test]
fn issues_report_the_per_rule_enumeration_cap() {
    let mut src = String::from("sort 人\npred 前提 : 人 → Prop\npred 结论 : 人 → Prop\n");
    for index in 0..10 {
        src.push_str(&format!("obj 人{index} : 人\n"));
    }
    src.push_str(
        "rule 规则 :\n  params p : 人\n  premise 前提 p\n  conclude 结论 p\n  source text \"测试\" locator \"规则\"\n",
    );
    let lib = load(&src);
    let r = reasoner(&lib);
    let limits = GapLimits {
        max_rule_attempts: 3,
        ..GapLimits::default()
    };
    let scan = r.issues_with(&limits).unwrap();
    assert_eq!(scan.issues.len(), 3, "only three instances are enumerated");
    assert!(
        scan.limits.contains(&GapLimit::RuleAttempts {
            rule: name("规则"),
            limit: 3,
        }),
        "the per-rule enumeration cap is reported: {:?}",
        scan.limits
    );
}
