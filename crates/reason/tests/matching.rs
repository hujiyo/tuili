//! Rule matching under adversarial but bounded shapes.
//!
//! Matching is recursive over terms and backtracks over premises, so it must
//! stay within the parser's declarative bounds: many variables but one matching
//! fact per premise, and deeply nested ground terms. These tests pin that such
//! rules match, derive and verify without panicking, hanging or losing the
//! structure of the term.

use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::Expr;
use std_deduce_lang::Library;
use std_deduce_reason::{verify, Reasoner};

fn load(src: &str) -> Library {
    let mut lib = Library::new();
    lib.load("matching", src)
        .unwrap_or_else(|error| panic!("load: {error}"));
    lib
}

fn reasoner(lib: &Library) -> Reasoner<'_> {
    let mut reasoner = Reasoner::new(&lib.env);
    reasoner
        .assume_ledger_axioms()
        .expect("ledger facts are assumptions");
    reasoner.saturate().expect("saturation must finish");
    reasoner
}

/// A rule with many parameters and premises, each premise matching exactly one
/// fact. This exercises the binding vector, the backtracking depth and the
/// conclusion instantiation without an exponential search.
#[test]
fn a_rule_with_many_variables_matches_and_derives() {
    const VARIABLES: usize = 32;

    let mut src = String::from("sort 公民\npred 全部满足 : Prop\n");
    for index in 0..VARIABLES {
        src.push_str(&format!(
            "pred 特征{index} : 公民 → Prop\nobj 甲{index} : 公民\n\
             axiom 事实{index} : 特征{index} 甲{index}\n  source text \"测试\" locator \"夹具\"\n"
        ));
    }
    src.push_str("rule 全部 :\n  params ");
    for index in 0..VARIABLES {
        if index > 0 {
            src.push_str(", ");
        }
        src.push_str(&format!("x{index} : 公民"));
    }
    src.push('\n');
    for index in 0..VARIABLES {
        src.push_str(&format!("  premise 特征{index} x{index}\n"));
    }
    src.push_str("  conclude 全部满足\n  source text \"测试\" locator \"夹具\"\n");

    let lib = load(&src);
    let reasoner = reasoner(&lib);
    let goal = Expr::constant("全部满足");
    assert!(
        reasoner.knows(&goal),
        "a fully matched rule must derive its conclusion"
    );

    let mut derivation = reasoner.derivation();
    derivation.root = reasoner.root_for(&goal);
    verify(&lib.env, &derivation).expect("the derivation must be legal");
}

/// A ground term nested forty applications deep must match a one-level
/// pattern, be substituted whole, and survive the independent verifier.
#[test]
fn a_deeply_nested_ground_term_matches_and_verifies() {
    const DEPTH: usize = 40;

    let mut source = String::from(
        "pred P : Prop → Prop\npred 已包裹 : Prop → Prop\n\
         axiom 命题常量 : Prop\n  source text \"测试\" locator \"夹具\"\n\
         axiom 深 : ",
    );
    source.push_str(&"P (".repeat(DEPTH));
    source.push_str("命题常量");
    source.push_str(&")".repeat(DEPTH));
    source.push_str(
        "\n  source text \"测试\" locator \"夹具\"\n\
         rule 包裹规则 :\n  params x : Prop\n  premise P x\n  conclude 已包裹 x\n\
         \x20 source text \"测试\" locator \"夹具\"\n",
    );

    let lib = load(&source);
    let reasoner = reasoner(&lib);

    // The premise `P x` matches the outer application of `深`; the rule
    // therefore concludes `已包裹` of the whole inner term (one binder fewer
    // than the fact), not of a flattened argument.
    let mut argument = Expr::constant("命题常量");
    for _ in 0..DEPTH - 1 {
        argument = Expr::app(Expr::constant("P"), argument);
    }
    let goal = Expr::app(Expr::constant("已包裹"), argument);
    assert!(
        reasoner.knows(&goal),
        "the whole nested term must be substituted, not flattened"
    );

    let mut derivation = reasoner.derivation();
    derivation.root = reasoner.root_for(&goal);
    verify(&lib.env, &derivation).expect("the nested instance must be legal");
}

/// A rule premise written through a `def` alias and a fact written with the
/// underlying predicate must match both ways round: the structural fast path
/// is not the only judgment, and the normalization fallback is not narrower
/// than the kernel's definitional equality.
///
/// Each case is one of the two writings; both must derive and pass the
/// independent verifier.
#[test]
fn a_definition_and_its_underlying_predicate_match_in_both_directions() {
    for def_premise in [true, false] {
        let premise = if def_premise {
            "夫妻 a b"
        } else {
            "配偶 a b"
        };
        let fact = if def_premise {
            "夫妻 张三 李四"
        } else {
            "配偶 张三 李四"
        };
        let src = format!(
            r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 须保护 : 人 → 人 → Prop
obj 张三 : 人
obj 李四 : 人
def 夫妻 : 人 → 人 → Prop := λ (a : 人) := λ (b : 人) := 配偶 a b
axiom 事实 : {fact}
  source text "测试" locator "夹具"
rule 夫妻保护 :
  params a : 人, b : 人
  premise {premise}
  conclude 须保护 a b
  source text "测试" locator "夹具"
"#
        );
        let lib = load(&src);
        let r = reasoner(&lib);
        let goal = Expr::apps(
            Expr::constant("须保护"),
            [Expr::constant("张三"), Expr::constant("李四")],
        );
        assert!(
            r.knows(&goal),
            "the premise `{premise}` must match the fact `{fact}`"
        );
        let mut derivation = r.derivation();
        derivation.root = r.root_for(&goal);
        verify(&lib.env, &derivation).expect("the matched instance must be legal");
    }
}

/// Two different `def` names for the same predicate feed each other: a rule
/// may conclude through one alias while the next rule consumes the other.
#[test]
fn two_equivalent_definition_aliases_feed_each_other() {
    let src = r#"
sort 人
pred 殴打 : 人 → 人 → Prop
pred 配偶 : 人 → 人 → Prop
pred 结论 : 人 → 人 → Prop
obj 张三 : 人
obj 李四 : 人
def 夫妻 : 人 → 人 → Prop := 配偶
def 配对 : 人 → 人 → Prop := 配偶
axiom 殴打事实 : 殴打 李四 张三
  source text "测试" locator "夹具"
rule 第一 :
  params a : 人, b : 人
  premise 殴打 b a
  conclude 夫妻 a b
  source text "测试" locator "夹具"
rule 第二 :
  params a : 人, b : 人
  premise 配对 a b
  conclude 结论 a b
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let goal = Expr::apps(
        Expr::constant("结论"),
        [Expr::constant("张三"), Expr::constant("李四")],
    );
    assert!(
        r.knows(&goal),
        "an alias conclusion must feed an alias premise"
    );
    let mut derivation = r.derivation();
    derivation.root = r.root_for(&goal);
    verify(&lib.env, &derivation).expect("the alias chain must be legal");
}

/// A nullary `def` is a proposition, not a function: it can be a premise and
/// must match the proposition its body names.
#[test]
fn a_nullary_definition_is_a_premise() {
    let src = r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 结论 : Prop
obj 张三 : 人
obj 李四 : 人
def 情形 : Prop := 配偶 张三 李四
axiom 事实 : 配偶 张三 李四
  source text "测试" locator "夹具"
rule 规则 :
  premise 情形
  conclude 结论
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let goal = Expr::constant("结论");
    assert!(
        r.knows(&goal),
        "a nullary definition must stand in for its body as a premise"
    );
    let mut derivation = r.derivation();
    derivation.root = r.root_for(&goal);
    verify(&lib.env, &derivation).expect("the nullary premise instance must be legal");
}

/// A rule whose conclusion is a `def` application can feed another rule whose
/// premise names the underlying predicate; the stored conclusion is the
/// written term, and matching sees through it.
#[test]
fn a_definition_conclusion_feeds_a_native_premise() {
    let src = r#"
sort 人
pred 殴打 : 人 → 人 → Prop
pred 配偶 : 人 → 人 → Prop
pred 须保护 : 人 → 人 → Prop
obj 张三 : 人
obj 李四 : 人
def 夫妻 : 人 → 人 → Prop := 配偶
def 配对 : 人 → 人 → Prop := 配偶
axiom 殴打事实 : 殴打 李四 张三
  source text "测试" locator "夹具"
rule 认定夫妻 :
  params a : 人, b : 人
  premise 殴打 b a
  conclude 夫妻 a b
  source text "测试" locator "夹具"
rule 保护夫妻 :
  params a : 人, b : 人
  premise 配偶 a b
  conclude 须保护 a b
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let goal = Expr::apps(
        Expr::constant("须保护"),
        [Expr::constant("张三"), Expr::constant("李四")],
    );
    assert!(
        r.knows(&goal),
        "a definition conclusion must match a native premise"
    );
    let mut derivation = r.derivation();
    derivation.root = r.root_for(&goal);
    verify(&lib.env, &derivation).expect("the definition-to-native chain must be legal");
}

/// A candidate that cannot fire lists its missing premise, printed as the
/// writer wrote it; the tree shows `缺 ⟨…⟩` instead of an empty candidate.
#[test]
fn a_mixed_writing_gap_lists_the_missing_premise() {
    let src = r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 须保护 : 人 → 人 → Prop
obj 张三 : 人
obj 李四 : 人
obj 王五 : 人
def 夫妻 : 人 → 人 → Prop := 配偶
axiom 事实 : 配偶 张三 李四
  source text "测试" locator "夹具"
rule 夫妻保护 :
  params a : 人, b : 人
  premise 夫妻 a b
  conclude 须保护 a b
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let goal = Expr::apps(
        Expr::constant("须保护"),
        [Expr::constant("李四"), Expr::constant("王五")],
    );
    assert!(!r.knows(&goal), "no fact supplies the instantiated premise");
    let tree = r.gap_tree(&goal).unwrap();
    assert_eq!(tree.candidates.len(), 1, "the rule is still a candidate");
    let candidate = &tree.candidates[0];
    assert_eq!(
        candidate.missing.len(),
        1,
        "a candidate that cannot fire must name the missing premise:\n{:?}",
        candidate.missing
    );
    assert_eq!(
        print_expr(&candidate.missing[0].premise),
        "夫妻 李四 王五",
        "the missing premise is reported as the writer wrote it"
    );
    assert!(
        candidate.missing[0].gap.is_some(),
        "the missing premise is expanded instead of silently dropped"
    );
}

/// One fact proves one proposition; a rule may need that proposition twice,
/// written once through the alias and once through the underlying predicate.
/// Facts are monotone, not linear, so one fact must be able to satisfy both
/// premises. Without reuse the candidate would list no missing premise while
/// the rule still could not fire.
#[test]
fn one_fact_satisfies_two_premises_writing_the_same_proposition() {
    let src = r#"
sort 人
pred 配偶 : 人 → 人 → Prop
pred 须保护 : 人 → 人 → Prop
obj 张三 : 人
obj 李四 : 人
def 夫妻 : 人 → 人 → Prop := 配偶
axiom 事实 : 配偶 张三 李四
  source text "测试" locator "夹具"
rule 规则 :
  params a : 人, b : 人
  premise 夫妻 a b
  premise 配偶 a b
  conclude 须保护 a b
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let goal = Expr::apps(
        Expr::constant("须保护"),
        [Expr::constant("张三"), Expr::constant("李四")],
    );
    assert!(
        r.knows(&goal),
        "one fact must satisfy both premises of the same proposition"
    );
    let mut derivation = r.derivation();
    derivation.root = r.root_for(&goal);
    verify(&lib.env, &derivation).expect("the reused-fact instance must be legal");
}
