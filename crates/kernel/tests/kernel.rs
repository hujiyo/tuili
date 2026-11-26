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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
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
        scope: Default::default(),
        occurred_at: None,
        occurred_in: None,
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
                scope: Default::default(),
                occurred_at: None,
                occurred_in: None,
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
    add(
        "h",
        DeclKind::Fact {
            identity: FactIdentity::Verified,
        },
        Expr::app(c("P"), c("甲")),
    );
    let rdecl = RuleDecl {
        guards: Vec::new(),
        params: vec![(name("x"), c("公民"))],
        premises: vec![(None, Expr::app(c("P"), Expr::Var(0)))],
        // The conclusion lives under the whole telescope: `x` is behind the
        // premise binder.
        conclusion: Expr::app(c("Q"), Expr::Var(1)),
        unlesses: vec![],
        exceptions: vec![],
        prefers: vec![],
        revision: None,
        sources: vec![],
        declared_in: None,
        burden: None,
        standard: None,
        exception_burden: None,
        exception_standard: None,
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
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    let bad_rule = RuleDecl {
        guards: Vec::new(),
        params: vec![],
        premises: vec![],
        // `侵犯` alone is a *function*, not a Prop.
        conclusion: c("侵犯"),
        unlesses: vec![],
        exceptions: vec![],
        prefers: vec![],
        revision: None,
        sources: vec![],
        declared_in: None,
        burden: None,
        standard: None,
        exception_burden: None,
        exception_standard: None,
    };
    let decl = Decl {
        name: name("坏规则"),
        kind: DeclKind::Rule(Box::new(bad_rule)),
        ty: Expr::Sort(0),
        sources: vec![],
        scope: Default::default(),
        occurred_at: None,
        occurred_in: None,
        index: 0,
    };
    assert!(env.insert(decl, &ctx).is_err());
}

#[test]
fn a_rule_with_duplicate_binder_names_is_refused() {
    // `p` is both a parameter and a premise binder. Apart from the collision
    // the rule is well-typed: `R p` and `P` are propositions, and `Q p` is a
    // proposition. But opening the telescope would turn both bindings into
    // the same `?p` constant, so the rule must not enter the ledger.
    let mut env = Env::new();
    let ctx = Ctx::new();
    for (n, ty) in [
        ("R", Expr::pi(Expr::Sort(0), Expr::Sort(0))),
        ("P", Expr::Sort(0)),
        ("Q", Expr::pi(Expr::Sort(0), Expr::Sort(0))),
    ] {
        env.insert(
            Decl {
                name: name(n),
                kind: DeclKind::Pred,
                ty,
                sources: vec![],
                scope: Default::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            },
            &ctx,
        )
        .unwrap();
    }
    let rule = RuleDecl {
        guards: Vec::new(),
        // p : Prop
        params: vec![(name("p"), Expr::Sort(0))],
        premises: vec![
            // r : R p
            (Some(name("r")), Expr::app(c("R"), Expr::Var(0))),
            // p : P
            (Some(name("p")), c("P")),
        ],
        // Q p, applied to the parameter behind the premise binders.
        conclusion: Expr::app(c("Q"), Expr::Var(2)),
        unlesses: vec![],
        exceptions: vec![],
        prefers: vec![],
        revision: None,
        sources: vec![],
        declared_in: None,
        burden: None,
        standard: None,
        exception_burden: None,
        exception_standard: None,
    };
    let decl = Decl {
        name: name("重名规则"),
        kind: DeclKind::Rule(Box::new(rule)),
        ty: Expr::Sort(0),
        sources: vec![],
        scope: Default::default(),
        occurred_at: None,
        occurred_in: None,
        index: 0,
    };
    let err = env
        .insert(decl, &ctx)
        .expect_err("duplicate telescope binders must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("binder `p`") && msg.contains("?p"),
        "the error should name the duplicated binder, got: {msg}"
    );
}

/// A top-level priority is a declaration of its own: it keeps the direction of
/// the relation, the declaring namespace and its provenance, and
/// `priorities()` lists it in insertion order.
#[test]
fn priorities_keep_direction_namespace_and_sources() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    for (winner, loser) in [("a.r1", "a.r2"), ("a.r2", "a.r3")] {
        env.insert(
            Decl {
                name: name(format!("priority:a:{winner}:{loser}")),
                kind: DeclKind::Priority {
                    winner: name(winner),
                    loser: name(loser),
                    declared_in: name("a"),
                },
                ty: Expr::Sort(0),
                sources: vec![std_deduce_kernel::env::SourceRef::new("上位法", "第一条")],
                scope: Default::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            },
            &ctx,
        )
        .unwrap();
    }
    let priorities = env.priorities();
    assert_eq!(priorities.len(), 2);
    assert_eq!(priorities[0].name.as_ref(), "priority:a:a.r1:a.r2");
    assert_eq!(priorities[0].winner.as_ref(), "a.r1");
    assert_eq!(priorities[0].loser.as_ref(), "a.r2");
    assert_eq!(priorities[0].declared_in.as_ref(), "a");
    assert_eq!(
        priorities[0].sources,
        vec![std_deduce_kernel::env::SourceRef::new("上位法", "第一条")]
    );
    assert_eq!(priorities[1].winner.as_ref(), "a.r2");
    assert_eq!(priorities[1].loser.as_ref(), "a.r3");
}

#[test]
fn source_one_line_keeps_the_existing_rendering() {
    let plain = std_deduce_kernel::env::SourceRef::new("宪法", "第三十九条");
    assert_eq!(plain.one_line(), "「宪法第三十九条」");

    let versioned = std_deduce_kernel::env::SourceRef::new("刑法", "第二十条").with_version("2020");
    assert_eq!(versioned.one_line(), "「刑法第二十条」（2020）");

    // Control characters are shown as escapes, so a source can never turn
    // one output line into several.
    let escaped = std_deduce_kernel::env::SourceRef::new("宪法\n第二版", "第三十九条\t")
        .with_version("2018\r");
    assert_eq!(
        escaped.one_line(),
        "「宪法\\n第二版第三十九条\\t」（2018\\r）"
    );
}

#[test]
fn source_one_line_distinguishes_a_literal_backslash_n_from_a_newline() {
    let literal = std_deduce_kernel::env::SourceRef::new("a\\nb", "");
    let newline = std_deduce_kernel::env::SourceRef::new("a\nb", "");
    assert_eq!(literal.one_line(), "「a\\\\nb」");
    assert_eq!(newline.one_line(), "「a\\nb」");
    assert_ne!(literal.one_line(), newline.one_line());
}

#[test]
fn source_one_line_escapes_invisible_formatting_characters() {
    let source = std_deduce_kernel::env::SourceRef::new("a\u{2028}b", "c\u{202E}d")
        .with_version("v\u{FEFF}");
    assert_eq!(
        source.one_line(),
        "「a\\u{2028}bc\\u{202E}d」（v\\u{FEFF}）"
    );

    let zero_width = std_deduce_kernel::env::SourceRef::new("a\u{200B}b", "");
    assert_eq!(zero_width.one_line(), "「a\\u{200B}b」");

    let empty = std_deduce_kernel::env::SourceRef::default();
    assert_eq!(empty.one_line(), "「」");
}

#[test]
fn source_full_prints_every_non_empty_field_and_escapes_control_characters() {
    let source = std_deduce_kernel::env::SourceRef {
        text: "中华人民共和国宪法".to_owned(),
        locator: "第三十九条".to_owned(),
        version: "2018".to_owned(),
        effective: Some("1982-12-04".to_owned()),
        note: "备注\r".to_owned(),
        quote: "中华人民共和国公民的住宅不受侵犯。\n禁止非法搜查。".to_owned(),
        url: "https://www.npc.gov.cn/law?article=39&lang=zh".to_owned(),
        jurisdiction: "CN".to_owned(),
        retrieved_at: "2026-11-21".to_owned(),
        hash: "sha256:abc".to_owned(),
    };
    let full = source.full();
    for needle in [
        "文本：中华人民共和国宪法",
        "条号：第三十九条",
        "版本：2018",
        "生效：1982-12-04",
        "引文：中华人民共和国公民的住宅不受侵犯。\\n禁止非法搜查。",
        "链接：https://www.npc.gov.cn/law?article=39&lang=zh",
        "管辖：CN",
        "抓取时间：2026-11-21",
        "哈希：sha256:abc",
        "备注：备注\\r",
    ] {
        assert!(full.contains(needle), "missing {needle:?} in:\n{full}");
    }
    assert!(!full.contains('\r'), "{full:?}");
    assert!(!full.contains("\n禁止"), "{full:?}");

    let sparse = std_deduce_kernel::env::SourceRef::new("宪法", "第三十九条");
    assert_eq!(sparse.full(), "文本：宪法\n条号：第三十九条");
}

/// A `Fact` asserts a proposition, so its declared type must be one.
#[test]
fn a_fact_must_assert_a_proposition() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    env.insert(
        Decl {
            name: name("公民"),
            kind: DeclKind::Sort,
            ty: Expr::Sort(1),
            sources: vec![],
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    // `公民` is a sort, not a proposition.
    let err = env
        .insert(
            Decl {
                name: name("坏事实"),
                kind: DeclKind::Fact {
                    identity: FactIdentity::Verified,
                },
                ty: c("公民"),
                sources: vec![],
                scope: Default::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            },
            &ctx,
        )
        .expect_err("a fact whose declared type is not a proposition must be refused");
    let msg = err.to_string();
    assert!(msg.contains("事实的类型必须是命题"), "got: {msg}");
}

/// An `Axiom` only names a constant, so it may not carry an asserted
/// proposition without an identity.
#[test]
fn an_axiom_must_not_assert_a_proposition() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    env.insert(
        Decl {
            name: name("公民"),
            kind: DeclKind::Sort,
            ty: Expr::Sort(1),
            sources: vec![],
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    env.insert(
        Decl {
            name: name("P"),
            kind: DeclKind::Pred,
            ty: Expr::pi(c("公民"), Expr::Sort(0)),
            sources: vec![],
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    env.insert(
        Decl {
            name: name("甲"),
            kind: DeclKind::Obj,
            ty: c("公民"),
            sources: vec![],
            scope: Default::default(),
            occurred_at: None,
            occurred_in: None,
            index: 0,
        },
        &ctx,
    )
    .unwrap();
    let err = env
        .insert(
            Decl {
                name: name("坏公理"),
                kind: DeclKind::Axiom,
                ty: Expr::app(c("P"), c("甲")),
                sources: vec![],
                scope: Default::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            },
            &ctx,
        )
        .expect_err("an axiom that asserts a proposition must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("断言命题必须用事实") && msg.contains("身份"),
        "got: {msg}"
    );
}

/// A `pred` is an atomic proposition once applied, so its declared type must
/// be a telescope ending in `Prop`. `人 → 人` is a function into a sort: it may
/// be a `def`, but it must not enter the ledger as a predicate.
#[test]
fn a_predicate_must_return_a_proposition() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    let add = |env: &mut Env, n: &str, kind: DeclKind, ty: Expr| {
        env.insert(
            Decl {
                name: name(n),
                kind,
                ty,
                sources: vec![],
                occurred_at: None,
                occurred_in: None,
                scope: Default::default(),
                index: 0,
            },
            &ctx,
        )
    };
    add(&mut env, "人", DeclKind::Sort, Expr::Sort(1)).unwrap();
    // A nullary predicate is a proposition; predicates over individuals and
    // higher-order predicates end in `Prop` as well.
    for (n, ty) in [
        ("天下雨", Expr::Sort(0)),
        ("好人", Expr::pi(c("人"), Expr::Sort(0))),
        ("关系", Expr::pi(c("人"), Expr::pi(c("人"), Expr::Sort(0)))),
    ] {
        add(&mut env, n, DeclKind::Pred, ty)
            .unwrap_or_else(|e| panic!("`{n}` must be accepted as a predicate: {e}"));
    }
    let err = add(&mut env, "坏人", DeclKind::Pred, Expr::pi(c("人"), c("人")))
        .expect_err("a predicate whose codomain is a sort must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("坏人"),
        "the error must name the declaration: {msg}"
    );
    assert!(
        msg.contains("Prop"),
        "the error must say the codomain must be Prop: {msg}"
    );
    assert!(
        msg.contains("人 → 人"),
        "the error must show the offending type: {msg}"
    );
    assert!(
        env.get("坏人").is_none(),
        "the refused declaration must not enter the ledger"
    );

    // A telescope whose final codomain is a proposition *term* is refused too:
    // `Π (x : 人), 天下雨` is the type of a proof of a universal proposition, not
    // a family of propositions, so it is not a predicate.
    let err = add(
        &mut env,
        "坏谓词",
        DeclKind::Pred,
        Expr::pi(c("人"), c("天下雨")),
    )
    .expect_err("a predicate whose codomain is a proposition term must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("坏谓词") && msg.contains("Prop"),
        "the error must name the declaration and the expected codomain: {msg}"
    );
    assert!(
        env.get("坏谓词").is_none(),
        "the refused declaration must not enter the ledger"
    );

    // A `def` alias is unfolded before the shape is checked: an alias of a
    // function into a sort is refused, an alias of a function into `Prop` is
    // accepted.
    add(
        &mut env,
        "函数类型",
        DeclKind::Def {
            body: Expr::pi(c("人"), c("人")),
        },
        Expr::Sort(1),
    )
    .unwrap();
    let err = add(&mut env, "别名坏事", DeclKind::Pred, c("函数类型"))
        .expect_err("an alias of `人 → 人` is still not a predicate");
    assert!(err.to_string().contains("别名坏事"), "{err}");
    add(
        &mut env,
        "谓词类型",
        DeclKind::Def {
            body: Expr::pi(c("人"), Expr::Sort(0)),
        },
        Expr::Sort(1),
    )
    .unwrap();
    add(&mut env, "别名好事", DeclKind::Pred, c("谓词类型"))
        .expect("an alias of `人 → Prop` is a predicate");
}

/// The five identities round-trip through their keyword and carry the
/// labels, strictness and derivation roles the fact ledger reports.
#[test]
fn fact_identities_round_trip_keywords_labels_and_roles() {
    let cases = [
        (FactIdentity::Verified, "verified", "法院查明", true, true),
        (
            FactIdentity::UserAsserted,
            "user_asserted",
            "用户陈述",
            false,
            true,
        ),
        (FactIdentity::Assumed, "assumed", "分析假设", false, true),
        (FactIdentity::Disputed, "disputed", "对方争议", false, false),
        (
            FactIdentity::Stipulated,
            "stipulated",
            "双方无争议",
            true,
            true,
        ),
    ];
    for (identity, keyword, label, strict, seeds) in cases {
        assert_eq!(identity.keyword(), keyword);
        assert_eq!(FactIdentity::from_keyword(keyword), Some(identity));
        assert_eq!(identity.label_zh(), label);
        assert_eq!(identity.is_strict(), strict, "{keyword} strictness");
        assert_eq!(identity.seeds_derivation(), seeds, "{keyword} seeds");
    }
    assert_eq!(FactIdentity::from_keyword("verifiedd"), None);
    assert_eq!(FactIdentity::from_keyword(""), None);
}

/// The burden and standard declarations round-trip through their written
/// labels, and the allowed set is exactly the three roles/standards. There is
/// deliberately no default: parsing an unknown label fails rather than falling
/// back to `claimant` or `preponderance`.
#[test]
fn burden_and_standard_round_trip_their_labels() {
    for (burden, label) in [
        (Burden::Claimant, "claimant"),
        (Burden::Respondent, "respondent"),
        (Burden::Court, "court"),
    ] {
        assert_eq!(burden.label(), label);
        assert_eq!(Burden::parse(label), Some(burden));
        assert!(
            Burden::labels().contains(&label),
            "the allowed set must list {label}"
        );
    }
    assert_eq!(Burden::labels().len(), 3);
    assert_eq!(Burden::parse("plaintiff"), None);
    assert_eq!(Burden::parse(""), None);

    for (standard, label) in [
        (Standard::Preponderance, "preponderance"),
        (Standard::ClearAndConvincing, "clear_and_convincing"),
        (Standard::BeyondReasonableDoubt, "beyond_reasonable_doubt"),
    ] {
        assert_eq!(standard.label(), label);
        assert_eq!(Standard::parse(label), Some(standard));
        assert!(
            Standard::labels().contains(&label),
            "the allowed set must list {label}"
        );
    }
    assert_eq!(Standard::labels().len(), 3);
    assert_eq!(Standard::parse("probable"), None);
    assert_eq!(Standard::parse(""), None);
}

/// The burden report text comes straight from the declaration. Chinese role
/// and standard labels are fixed here; a missing value is written out as
/// `未声明举证责任` / `未声明证明标准` rather than defaulted, and the standard
/// never becomes a number.
#[test]
fn burden_report_spells_out_declared_and_undeclared_values() {
    for (burden, keyword, label, actor) in [
        (Burden::Claimant, "claimant", "主张方", "主张方提出"),
        (Burden::Respondent, "respondent", "相对方", "相对方提出"),
        (Burden::Court, "court", "法院职权", "法院依职权查明"),
    ] {
        assert_eq!(burden.label(), keyword);
        assert_eq!(burden.label_zh(), label);
        assert_eq!(burden.actor_zh(), actor);
    }
    for (standard, keyword, label) in [
        (Standard::Preponderance, "preponderance", "优势证据"),
        (
            Standard::ClearAndConvincing,
            "clear_and_convincing",
            "清楚可信",
        ),
        (
            Standard::BeyondReasonableDoubt,
            "beyond_reasonable_doubt",
            "排除合理怀疑",
        ),
    ] {
        assert_eq!(standard.label(), keyword);
        assert_eq!(standard.label_zh(), label);
    }

    let both = ProofBurden {
        burden: Some(Burden::Claimant),
        standard: Some(Standard::Preponderance),
    };
    assert_eq!(both.labels_zh(), ("主张方", "优势证据"));
    assert_eq!(both.pair_zh(), "主张方 / 优势证据");
    assert_eq!(
        both.sentence_zh(false),
        "这条证据由主张方提出，标准是优势证据"
    );
    assert_eq!(both.sentence_zh(true), "例外由主张方提出，标准是优势证据");

    let court = ProofBurden {
        burden: Some(Burden::Court),
        standard: Some(Standard::ClearAndConvincing),
    };
    assert_eq!(
        court.sentence_zh(false),
        "这条证据由法院依职权查明，标准是清楚可信",
        "a court's own inquiry is not a party presenting evidence"
    );
    assert_eq!(
        court.sentence_zh(true),
        "例外由法院依职权查明，标准是清楚可信"
    );

    let burden_only = ProofBurden {
        burden: Some(Burden::Respondent),
        standard: None,
    };
    assert_eq!(
        burden_only.pair_zh(),
        "相对方 / 未声明证明标准",
        "an undeclared standard is not defaulted"
    );
    assert_eq!(
        burden_only.sentence_zh(false),
        "这条证据由相对方提出，但未声明证明标准"
    );

    let standard_only = ProofBurden {
        burden: None,
        standard: Some(Standard::BeyondReasonableDoubt),
    };
    assert_eq!(
        standard_only.pair_zh(),
        "未声明举证责任 / 排除合理怀疑",
        "an undeclared burden is not defaulted to the claimant"
    );
    assert_eq!(
        standard_only.sentence_zh(false),
        "这条证据未声明举证责任，标准是排除合理怀疑"
    );

    let neither = ProofBurden::default();
    assert_eq!(neither.pair_zh(), "未声明举证责任 / 未声明证明标准");
    assert_eq!(
        neither.sentence_zh(false),
        "这条证据未声明举证责任，未声明证明标准"
    );
    assert_eq!(
        neither.sentence_zh(true),
        "例外未声明举证责任，未声明证明标准"
    );
    for text in [neither.pair_zh(), neither.sentence_zh(false)] {
        assert!(
            !text.chars().any(|ch| ch.is_ascii_digit()),
            "the standard report must not attach a number: {text}"
        );
    }
}

/// `revision` groups are keyed by their scope plus the written identifier, and
/// only rules that declared one belong to a group.
///
/// A module's scope is its namespace; a case file's scope is the file's load
/// identity, so two case files may each group their own `第二十条` versions
/// without merging. The kernel stores the relation and never chooses a version:
/// the view is what reports and the loader read.
#[test]
fn revision_groups_are_keyed_by_scope_and_identifier() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    let add = |env: &mut Env, name: &str, kind: DeclKind, ty: Expr| {
        env.insert(
            Decl {
                name: std_deduce_kernel::name(name),
                kind,
                ty,
                sources: vec![],
                scope: Default::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            },
            &ctx,
        )
        .unwrap();
    };
    add(&mut env, "P", DeclKind::Pred, Expr::Sort(0));
    let add_rule = |env: &mut Env,
                    name: &str,
                    namespace: Option<&str>,
                    file: Option<&str>,
                    revision: Option<&str>| {
        let group = revision.map(|revision| RevisionGroup {
            scope: match namespace {
                Some(namespace) => RevisionScope::Namespace(std_deduce_kernel::name(namespace)),
                None => RevisionScope::File(std_deduce_kernel::name(
                    file.expect("a case rule's group needs the file identity"),
                )),
            },
            revision: std_deduce_kernel::name(revision),
        });
        let decl = RuleDecl {
            guards: Vec::new(),
            params: vec![],
            premises: vec![],
            conclusion: Expr::constant("P"),
            unlesses: vec![],
            exceptions: vec![],
            prefers: vec![],
            revision: group,
            sources: vec![],
            declared_in: namespace.map(std_deduce_kernel::name),
            burden: None,
            standard: None,
            exception_burden: None,
            exception_standard: None,
        };
        let ty = std_deduce_kernel::env::rule_type(&decl);
        env.insert(
            Decl {
                name: std_deduce_kernel::name(name),
                kind: DeclKind::Rule(Box::new(decl)),
                ty,
                sources: vec![],
                scope: Default::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            },
            &ctx,
        )
        .unwrap();
    };
    add_rule(&mut env, "a.旧", Some("a"), None, Some("第二十条"));
    add_rule(&mut env, "a.新", Some("a"), None, Some("第二十条"));
    add_rule(&mut env, "b.旧", Some("b"), None, Some("第二十条"));
    add_rule(&mut env, "b.新", Some("b"), None, Some("第二十条"));
    add_rule(&mut env, "无关", Some("b"), None, None);
    // Two case files, each grouping its own two versions under the same
    // identifier. They are two groups, not one formed across the files.
    add_rule(
        &mut env,
        "案件一.旧",
        None,
        Some("c1.std"),
        Some("第二十条"),
    );
    add_rule(
        &mut env,
        "案件一.新",
        None,
        Some("c1.std"),
        Some("第二十条"),
    );
    add_rule(
        &mut env,
        "案件二.旧",
        None,
        Some("c2.std"),
        Some("第二十条"),
    );
    add_rule(
        &mut env,
        "案件二.新",
        None,
        Some("c2.std"),
        Some("第二十条"),
    );

    assert_eq!(
        env.revision_group_of(&std_deduce_kernel::name("a.旧"))
            .map(|group| group.label()),
        Some("a.第二十条".to_owned())
    );
    assert_eq!(
        env.revision_group_of(&std_deduce_kernel::name("无关")),
        None,
        "a rule without `revision` belongs to no group"
    );
    let groups = env.revision_groups();
    assert_eq!(groups.len(), 4);
    assert_eq!(groups[0].0.label(), "a.第二十条");
    assert_eq!(
        groups[0].1,
        vec![
            std_deduce_kernel::name("a.旧"),
            std_deduce_kernel::name("a.新"),
        ]
    );
    assert_eq!(groups[1].0.label(), "b.第二十条");
    assert_eq!(
        groups[1].1,
        vec![
            std_deduce_kernel::name("b.旧"),
            std_deduce_kernel::name("b.新"),
        ],
        "the rule without a revision is not a member"
    );
    // A case-file group prints the identifier alone, but its identity is the
    // pair of the file identity and the identifier: the two groups below are
    // distinct even though they print the same label.
    assert_eq!(groups[2].0.label(), "第二十条");
    assert_eq!(
        groups[2].0.scope_name().as_ref(),
        "c1.std",
        "the case group's scope is the file it was loaded from"
    );
    assert_eq!(groups[3].0.label(), "第二十条");
    assert_eq!(
        groups[3].0.scope_name().as_ref(),
        "c2.std",
        "two case files never share a revision group"
    );
    assert_ne!(groups[2].0, groups[3].0);
}
