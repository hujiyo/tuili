//! Kernel tests. These are the golden cases: any change that breaks one of
//! these has broken the trust boundary, whatever the feature was.

use std_deduce_kernel::*;

fn c(s: &str) -> Expr {
    Expr::constant(s)
}

#[test]
fn sorts_form_a_predicative_chain() {
    let env = Env::new();
    let ctx = Ctx::new();
    assert_eq!(
        check::infer(&env, &ctx, &Expr::Sort(0)).unwrap(),
        Expr::Sort(1)
    );
    assert_eq!(
        check::infer(&env, &ctx, &Expr::Sort(3)).unwrap(),
        Expr::Sort(4)
    );
}

#[test]
fn identity_function_checks() {
    let env = Env::new();
    let ctx = Ctx::new();
    // fun (A : Type) (x : A) => x
    let id = Expr::lam(
        "A",
        Expr::Sort(1),
        Expr::lam("x", Expr::Var(0), Expr::Var(0)),
    );
    let ty = Expr::forall(
        "A",
        Expr::Sort(1),
        Expr::forall("x", Expr::Var(0), Expr::Var(0)),
    );
    check::check(&env, &ctx, &id, &ty).unwrap();
}

#[test]
fn applying_the_identity_works() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    // Pa : Prop. Then (fun (x : Prop) => x) Pa : Prop.
    env.insert(
        Decl {
            name: name("Pa"),
            kind: DeclKind::Axiom,
            ty: Expr::Sort(0),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    let app = Expr::app(Expr::lam("x", Expr::Sort(0), Expr::Var(0)), c("Pa"));
    assert_eq!(check::infer(&env, &ctx, &app).unwrap(), Expr::Sort(0));
}

#[test]
fn dependent_application_substitutes() {
    // Define `P : Prop → Prop`, `a : Prop`; applying `P a` must yield Prop,
    // and the argument must be checked against Prop, not assumed.
    let mut env = Env::new();
    let ctx = Ctx::new();
    env.insert(
        Decl {
            name: name("P"),
            kind: DeclKind::Axiom,
            ty: Expr::pi(Expr::Sort(0), Expr::Sort(0)),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    env.insert(
        Decl {
            name: name("a"),
            kind: DeclKind::Axiom,
            ty: Expr::Sort(0),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    check::check(&env, &ctx, &c("P"), &Expr::pi(Expr::Sort(0), Expr::Sort(0))).unwrap();
    check::check(&env, &ctx, &Expr::app(c("P"), c("a")), &Expr::Sort(0)).unwrap();
}

#[test]
fn rejects_wrong_argument_type() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    env.insert(
        Decl {
            name: name("P"),
            // P : Prop -> Prop
            kind: DeclKind::Axiom,
            ty: Expr::pi(Expr::Sort(0), Expr::Sort(0)),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    // P expects a Prop; `Sort 1` (Type) is of sort `Sort 2`, so this fails.
    let bad = Expr::app(c("P"), Expr::Sort(1));
    assert!(check::infer(&env, &ctx, &bad).is_err());
}

#[test]
fn no_type_in_type() {
    // Sort 0 : Sort 1, so Sort 0 itself must NOT check against Sort 0.
    let env = Env::new();
    let ctx = Ctx::new();
    assert!(check::check(&env, &ctx, &Expr::Sort(0), &Expr::Sort(0)).is_err());
}

/// Prop is impredicative: quantifying over *individuals* still yields a
/// proposition. Without this, `∀ (x : 公民), 受教育权 x` is a `Type`, so
/// "every citizen has the right to education" cannot be stated as a fact.
#[test]
fn forall_over_individuals_stays_in_prop() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    env.insert(
        Decl {
            name: name("公民"),
            kind: DeclKind::Sort,
            ty: Expr::Sort(1),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    // 受教育权 : 公民 → Prop
    env.insert(
        Decl {
            name: name("受教育权"),
            kind: DeclKind::Pred,
            ty: Expr::pi(Expr::Sort(1), Expr::Sort(0)),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    let statement = Expr::pi(Expr::Sort(1), Expr::app(c("受教育权"), Expr::Var(0)));
    assert_eq!(
        check::infer(&env, &ctx, &statement).unwrap(),
        Expr::Sort(0),
        "a quantified statement about individuals must be a proposition"
    );
    // And so it can be asserted as a fact.
    check::check(&env, &ctx, &statement, &Expr::Sort(0)).unwrap();
}

/// Impredicativity must not leak into the `Type` hierarchy: `Type` still
/// cannot contain itself.
#[test]
fn types_stay_predicative() {
    let env = Env::new();
    let ctx = Ctx::new();
    // `∀ (A : Type), A` — domain is Type (Sort 1), codomain `A` is Sort 1.
    let statement = Expr::pi(Expr::Sort(1), Expr::Var(0));
    assert_eq!(
        check::infer(&env, &ctx, &statement).unwrap(),
        Expr::Sort(2),
        "a quantifier over Type must land in Type 1, not stay in Type"
    );
}

#[test]
fn definition_unfolds_under_conversion() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    // def T : Type := Prop
    env.insert(
        Decl {
            name: name("T"),
            kind: DeclKind::Def {
                body: Expr::Sort(0),
            },
            ty: Expr::Sort(1),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    // T and Prop must be definitionally equal.
    assert!(conv::convertible(&env, &ctx, &c("T"), &Expr::Sort(0)).unwrap());
    // Therefore a value of type T can be checked against type Prop.
    env.insert(
        Decl {
            name: name("p"),
            kind: DeclKind::Axiom,
            ty: c("T"),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    check::check(&env, &ctx, &c("p"), &Expr::Sort(0)).unwrap();
}

#[test]
fn eta_holds_for_lambdas() {
    let env = Env::new();
    let ctx = Ctx::new();
    // fun (x : Prop) => x   ==   (fun (y : Prop) => y)
    let f = Expr::lam("x", Expr::Sort(0), Expr::Var(0));
    let g = Expr::lam("y", Expr::Sort(0), Expr::Var(0));
    assert!(conv::convertible(&env, &ctx, &f, &g).unwrap());
}

#[test]
fn duplicate_names_are_refused() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    let d = || Decl {
        name: name("x"),
        kind: DeclKind::Axiom,
        ty: Expr::Sort(0),
        sources: vec![],
        index: 0,
    };
    env.insert(d(), &ctx).unwrap();
    assert!(matches!(
        env.insert(d(), &ctx),
        Err(Error::DuplicateName(_))
    ));
}

/// The environment shared by the rule-constant tests: `公民`;
/// `P Q : 公民 → Prop`; `甲 : 公民`; `h : P 甲`; and the rule
/// `r : ∀ (x : 公民), P x → Q x`.
fn rule_constant_env() -> Env {
    let mut env = Env::new();
    let ctx = Ctx::new();
    let mut add = |n: &str, kind: DeclKind, ty: Expr| {
        env.insert(
            Decl {
                name: name(n),
                kind,
                ty,
                sources: vec![],
                index: 0,
            },
            &ctx,
        )
        .unwrap();
    };
    add("公民", DeclKind::Sort, Expr::Sort(1));
    add("P", DeclKind::Pred, Expr::pi(c("公民"), Expr::Sort(0)));
    add("Q", DeclKind::Pred, Expr::pi(c("公民"), Expr::Sort(0)));
    add("甲", DeclKind::Obj, c("公民"));
    add("h", DeclKind::Axiom, Expr::app(c("P"), c("甲")));
    let rdecl = RuleDecl {
        params: vec![(name("x"), c("公民"))],
        premises: vec![(None, Expr::app(c("P"), Expr::Var(0)))],
        // The conclusion lives under the whole telescope: `x` is behind the
        // premise binder.
        conclusion: Expr::app(c("Q"), Expr::Var(1)),
        unlesses: vec![],
        exceptions: vec![],
        prefers: vec![],
        sources: vec![],
    };
    let ty = std_deduce_kernel::env::rule_type(&rdecl);
    add("r", DeclKind::Rule(Box::new(rdecl)), ty);
    env
}

#[test]
fn rule_constant_applies_to_prove_its_conclusion() {
    let env = rule_constant_env();
    let ctx = Ctx::new();
    let r_ty = check::infer(&env, &ctx, &c("r")).unwrap();
    let expected = Expr::forall(
        "x",
        c("公民"),
        Expr::pi(
            Expr::app(c("P"), Expr::Var(0)),
            Expr::app(c("Q"), Expr::Var(1)),
        ),
    );
    assert!(
        conv::convertible(&env, &ctx, &r_ty, &expected).unwrap(),
        "rule constant must have type `∀ x : 公民, P x → Q x`, got `{r_ty}`"
    );
    let proof = Expr::apps(c("r"), [c("甲"), c("h")]);
    let proof_ty = check::infer(&env, &ctx, &proof).unwrap();
    let conclusion = Expr::app(c("Q"), c("甲"));
    assert!(
        conv::convertible(&env, &ctx, &proof_ty, &conclusion).unwrap(),
        "applying the rule to every argument must yield `Q 甲`, got `{proof_ty}`"
    );
    check::check(&env, &ctx, &proof, &conclusion).unwrap();
}

#[test]
fn rule_constant_needs_every_premise_and_is_not_a_prop() {
    let env = rule_constant_env();
    let ctx = Ctx::new();
    // Supplying only the parameter leaves a function waiting for the premise.
    let partial = Expr::apps(c("r"), [c("甲")]);
    let partial_ty = check::infer(&env, &ctx, &partial).unwrap();
    let missing = Expr::pi(Expr::app(c("P"), c("甲")), Expr::app(c("Q"), c("甲")));
    assert!(
        conv::convertible(&env, &ctx, &partial_ty, &missing).unwrap(),
        "`r 甲` must have type `P 甲 → Q 甲`, got `{partial_ty}`"
    );
    assert!(
        !conv::convertible(&env, &ctx, &partial_ty, &Expr::app(c("Q"), c("甲"))).unwrap(),
        "`r 甲` must not already be a proof of `Q 甲`"
    );
    // A proof of a proposition is not itself a proposition.
    let proof = Expr::apps(c("r"), [c("甲"), c("h")]);
    assert!(
        check::check(&env, &ctx, &proof, &Expr::Sort(0)).is_err(),
        "`r 甲 h` proves `Q 甲`; it is not a proof of `Prop`"
    );
}

#[test]
fn a_rule_must_be_well_typed() {
    // A rule whose conclusion is not a proposition must be refused.
    let mut env = Env::new();
    let ctx = Ctx::new();
    env.insert(
        Decl {
            name: name("侵犯"),
            kind: DeclKind::Pred,
            ty: Expr::forall("x", Expr::Sort(0), Expr::Sort(0)),
            sources: vec![],
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    let bad_rule = RuleDecl {
        params: vec![],
        premises: vec![],
        // `侵犯` alone is a *function*, not a Prop.
        conclusion: c("侵犯"),
        unlesses: vec![],
        exceptions: vec![],
        prefers: vec![],
        sources: vec![],
    };
    let decl = Decl {
        name: name("坏规则"),
        kind: DeclKind::Rule(Box::new(bad_rule)),
        ty: Expr::Sort(0),
        sources: vec![],
        index: 0,
    };
    assert!(env.insert(decl, &ctx).is_err());
}
