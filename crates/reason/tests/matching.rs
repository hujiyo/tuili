//! Rule matching under adversarial but bounded shapes.
//!
//! Matching is recursive over terms and backtracks over premises, so it must
//! stay within the parser's declarative bounds: many variables but one matching
//! fact per premise, and deeply nested ground terms. These tests pin that such
//! rules match, derive and verify without panicking, hanging or losing the
//! structure of the term.

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
