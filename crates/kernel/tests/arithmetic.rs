//! Exact-integer arithmetic in the kernel: literals, evaluation, overflow,
//! comparisons and the built-in name reservation.

use std_deduce_kernel::builtin;
use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::error::Error;
use std_deduce_kernel::norm::{evaluate_arithmetic, normalize, whnf};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::*;

fn op(name: &str, arguments: Vec<Expr>) -> Expr {
    Expr::apps(Expr::constant(name), arguments)
}

fn c(name: &str) -> Expr {
    Expr::constant(name)
}

fn num(value: i64) -> Expr {
    Expr::Num(value)
}

fn decl(kind: DeclKind, name: &str, ty: Expr) -> Decl {
    Decl {
        name: name.into(),
        kind,
        ty,
        sources: vec![],
        scope: Default::default(),
        occurred_at: None,
        occurred_in: None,
        index: 0,
    }
}

/// `sort 人`, `def 金额 : Type := Int` and an individual `甲`, with the two
/// amount predicates the tests use.
fn amount_env() -> Env {
    let ctx = Ctx::new();
    let mut env = Env::new();
    env.insert(decl(DeclKind::Sort, "人", Expr::Sort(1)), &ctx)
        .unwrap();
    env.insert(
        decl(DeclKind::Def { body: c("Int") }, "金额", Expr::Sort(1)),
        &ctx,
    )
    .unwrap();
    let amount = c("金额");
    for predicate in ["医疗费", "合计"] {
        env.insert(
            decl(
                DeclKind::Pred,
                predicate,
                Expr::pi(c("人"), Expr::pi(amount.clone(), Expr::Sort(0))),
            ),
            &ctx,
        )
        .unwrap();
    }
    env.insert(decl(DeclKind::Obj, "甲", c("人")), &ctx)
        .unwrap();
    env
}

#[test]
fn a_literal_is_an_int() {
    let env = Env::new();
    let ctx = Ctx::new();
    assert_eq!(
        check::infer(&env, &ctx, &num(5000)).expect("a literal has a type"),
        Expr::constant(builtin::INT)
    );
    assert_eq!(
        check::infer(&env, &ctx, &Expr::constant(builtin::INT)).expect("Int has a type"),
        Expr::Sort(1)
    );
}

#[test]
fn the_built_in_operations_evaluate_in_whnf() {
    let env = Env::new();
    assert_eq!(
        whnf(&env, &op(builtin::ADD, vec![num(3000), num(2000)])).expect("whnf"),
        num(5000)
    );
    assert_eq!(
        whnf(&env, &op(builtin::SUB, vec![num(3), num(5)])).expect("whnf"),
        num(-2)
    );
    assert_eq!(
        whnf(&env, &op(builtin::MUL, vec![num(6), num(7)])).expect("whnf"),
        num(42)
    );
    assert_eq!(
        whnf(&env, &op(builtin::NEG, vec![num(5000)])).expect("whnf"),
        num(-5000)
    );
}

#[test]
fn nested_arithmetic_evaluates_inside_whnf() {
    let env = Env::new();
    // (3 * 4) + 5
    let term = op(
        builtin::ADD,
        vec![op(builtin::MUL, vec![num(3), num(4)]), num(5)],
    );
    assert_eq!(whnf(&env, &term).expect("whnf"), num(17));
}

#[test]
fn a_partially_applied_operation_stays_neutral() {
    let env = Env::new();
    let partial = op(builtin::ADD, vec![num(3)]);
    assert_eq!(whnf(&env, &partial).expect("whnf"), partial);
    // An operand that is not a literal leaves the operation neutral as well.
    let open = op(builtin::ADD, vec![c("?a"), c("?b")]);
    assert_eq!(whnf(&env, &open).expect("whnf"), open);
}

#[test]
fn overflow_is_an_error_not_a_wraparound() {
    let env = Env::new();
    let add = op(builtin::ADD, vec![num(i64::MAX), num(1)]);
    let error = whnf(&env, &add).expect_err("i64::MAX + 1 must be refused");
    assert!(matches!(error, Error::Other(_)), "{error}");
    assert!(error.to_string().contains("溢出"), "{error}");
    assert!(error.to_string().contains(&i64::MAX.to_string()), "{error}");

    assert!(whnf(&env, &op(builtin::MUL, vec![num(i64::MAX), num(2)])).is_err());
    assert!(whnf(&env, &op(builtin::SUB, vec![num(i64::MIN), num(1)])).is_err());
    assert!(whnf(&env, &op(builtin::NEG, vec![num(i64::MIN)])).is_err());
}

#[test]
fn comparisons_reduce_to_true_or_false() {
    let env = Env::new();
    let ctx = Ctx::new();
    assert_eq!(
        whnf(&env, &op(builtin::LESS, vec![num(3000), num(5000)])).expect("whnf"),
        Expr::constant(builtin::TRUE)
    );
    assert_eq!(
        whnf(&env, &op(builtin::LE, vec![num(5000), num(5000)])).expect("whnf"),
        Expr::constant(builtin::TRUE)
    );
    assert_eq!(
        whnf(&env, &op(builtin::LESS, vec![num(5000), num(3000)])).expect("whnf"),
        Expr::constant(builtin::FALSE)
    );
    assert!(convertible(
        &env,
        &ctx,
        &op(builtin::LESS, vec![num(3), num(5)]),
        &Expr::constant(builtin::TRUE)
    )
    .expect("conversion decides"));
    assert!(convertible(&env, &ctx, &num(5), &num(5)).expect("literals compare exactly"));
    assert!(!convertible(&env, &ctx, &num(5), &num(6)).expect("different literals differ"));
}

#[test]
fn a_comparison_of_non_literals_stays_neutral() {
    let env = Env::new();
    let term = op(builtin::LESS, vec![c("?a"), num(5)]);
    assert_eq!(whnf(&env, &term).expect("whnf"), term);
}

#[test]
fn arithmetic_evaluates_terms_but_leaves_declarations_opaque() {
    let env = amount_env();
    // `合计 甲 (add 3000 2000)` -> `合计 甲 5000`.
    let total = Expr::apps(
        c("合计"),
        [c("甲"), op(builtin::ADD, vec![num(3000), num(2000)])],
    );
    assert_eq!(
        evaluate_arithmetic(&env, &total).expect("evaluation succeeds"),
        Expr::apps(c("合计"), [c("甲"), num(5000)])
    );
    assert_eq!(
        print_expr(&evaluate_arithmetic(&env, &total).expect("evaluation succeeds")),
        "合计 甲 5000"
    );
    // A `def` that is not an operation is not unfolded by the arithmetic
    // evaluation: only the numbers inside a term change.
    let aliased = Expr::apps(c("医疗费"), [c("甲"), c("金额")]);
    assert_eq!(
        evaluate_arithmetic(&env, &aliased).expect("evaluation succeeds"),
        aliased
    );
}

#[test]
fn a_def_alias_of_a_literal_is_unfolded_for_the_value() {
    let ctx = Ctx::new();
    let mut env = Env::new();
    env.insert(decl(DeclKind::Sort, "人", Expr::Sort(1)), &ctx)
        .unwrap();
    env.insert(
        decl(DeclKind::Def { body: num(3000) }, "标准金额", c("Int")),
        &ctx,
    )
    .unwrap();
    let term = op(builtin::ADD, vec![c("标准金额"), num(2000)]);
    assert_eq!(whnf(&env, &term).expect("whnf"), num(5000));
}

#[test]
fn normalize_evaluates_arithmetic_reached_after_normalizing_arguments() {
    let env = Env::new();
    let ctx = Ctx::new();
    // `(fun x => x) 2 + 3` — beta must reduce the argument first, then the
    // addition sees two literals.
    let argument = Expr::app(Expr::lam("x", Expr::Sort(0), Expr::Var(0)), num(2));
    let term = op(builtin::ADD, vec![argument, num(3)]);
    assert_eq!(normalize(&env, &ctx, &term).expect("normalize"), num(5));
}

#[test]
fn a_definition_cannot_shadow_a_built_in_name() {
    let ctx = Ctx::new();
    let mut env = Env::new();
    for reserved in builtin::NAMES {
        let error = env
            .insert(
                decl(
                    DeclKind::Def { body: num(0) },
                    reserved,
                    Expr::constant(builtin::INT),
                ),
                &ctx,
            )
            .expect_err("a built-in name cannot be declared");
        assert!(error.to_string().contains("内建名称"), "{error}");
    }
}

#[test]
fn a_declaration_with_an_overflowing_literal_is_refused_at_load() {
    let ctx = Ctx::new();
    let mut env = amount_env();
    let overflowing = Expr::apps(
        c("合计"),
        [c("甲"), op(builtin::ADD, vec![num(i64::MAX), num(1)])],
    );
    let error = env
        .insert(
            decl(
                DeclKind::Fact {
                    identity: FactIdentity::Verified,
                },
                "溢出事实",
                overflowing,
            ),
            &ctx,
        )
        .expect_err("an overflowing closed expression cannot be declared");
    assert!(error.to_string().contains("溢出"), "{error}");

    let huge = Expr::apps(c("合计"), [c("甲"), num(i64::MAX)]);
    env.insert(
        decl(
            DeclKind::Fact {
                identity: FactIdentity::Verified,
            },
            "大额事实",
            huge,
        ),
        &ctx,
    )
    .expect("a large literal without arithmetic is allowed");
}

#[test]
fn a_comparison_cannot_be_a_rule_premise_or_blocker() {
    // A comparison is a computed expression, not a proposition a fact can
    // prove. Letting `less a b` stand as a premise would turn "it evaluated to
    // True" into evidence, so the rule is refused at load time.
    let ctx = Ctx::new();
    let mut env = Env::new();
    env.insert(
        decl(DeclKind::Pred, "小", Expr::pi(c("Int"), Expr::Sort(0))),
        &ctx,
    )
    .unwrap();
    let rule_with = |premises: Vec<(Option<Name>, Expr)>, unlesses: Vec<Expr>| RuleDecl {
        params: vec![(name("a"), c("Int"))],
        premises,
        conclusion: Expr::apps(c("小"), [Expr::Var(0)]),
        unlesses,
        burden: None,
        standard: None,
        exception_burden: None,
        exception_standard: None,
        exceptions: Vec::new(),
        prefers: Vec::new(),
        sources: Vec::new(),
        declared_in: None,
    };
    let comparison = op(builtin::LESS, vec![Expr::Var(0), num(5000)]);
    let error = rule_with(vec![(None, comparison.clone())], Vec::new())
        .check(&env, &Expr::Sort(0))
        .expect_err("a comparison premise must be refused");
    assert!(
        error.to_string().contains("比较目前不参与规则触发"),
        "{error}"
    );
    assert!(error.to_string().contains("前提 1"), "{error}");

    let error = rule_with(Vec::new(), vec![comparison])
        .check(&env, &Expr::Sort(0))
        .expect_err("a comparison unless must be refused");
    assert!(error.to_string().contains("unless 1"), "{error}");
}

#[test]
fn the_type_of_an_amount_alias_accepts_a_literal() {
    let ctx = Ctx::new();
    let env = amount_env();
    // `医疗费 甲 3000` is a proposition: the literal's `Int` and the predicate's
    // `金额` are the same type, because `金额` is `def 金额 := Int`.
    let proposition = Expr::apps(c("医疗费"), [c("甲"), num(3000)]);
    check::check(&env, &ctx, &proposition, &Expr::Sort(0)).expect("the amount fits its parameter");
    // A literal where an individual is expected is a type error, not a
    // silent coercion.
    let wrong = Expr::apps(c("医疗费"), [num(3000), num(3000)]);
    assert!(check::check(&env, &ctx, &wrong, &Expr::Sort(0)).is_err());
}
