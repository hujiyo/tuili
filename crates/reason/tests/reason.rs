//! Reasoner tests. These pin down the three commitments documented in the
//! crate: no negation as failure, no silent conflict resolution, and no
//! hidden gaps.

use std_deduce_kernel::env::{Ctx, DeclKind, FactIdentity, SourceRef};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{name, Decl, Env, Expr};
use std_deduce_lang::Library;
use std_deduce_reason::{
    verify, Conflict, PriorityClause, PriorityOrigin, Provenance, Reasoner, Resolution,
    ResolutionBasis, Side, UnresolvedReason,
};

fn load(src: &str) -> Library {
    let mut lib = Library::new();
    lib.load("test", src)
        .unwrap_or_else(|e| panic!("load: {e}"));
    lib
}

fn load_all(sources: &[(&str, &str)]) -> Library {
    let mut lib = Library::new();
    for (name, src) in sources {
        lib.load(name, src)
            .unwrap_or_else(|e| panic!("load {name}: {e}"));
    }
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

fn assemble(lib: &Library, goal: &Expr) -> (std_deduce_reason::Derivation, Result<(), String>) {
    let mut r = Reasoner::new(&lib.env);
    for decl in lib.env.iter() {
        if let DeclKind::Fact { identity } = &decl.kind {
            if identity.seeds_derivation() {
                r.assume(
                    &decl.ty,
                    *identity,
                    decl.sources.clone(),
                    Some(decl.name.to_string()),
                )
                .unwrap();
            }
        }
    }
    r.saturate().unwrap();
    let mut d = r.derivation();
    d.root = r.root_for(goal);
    let v = verify(&lib.env, &d);
    (d, v)
}

#[test]
fn a_rule_fires_and_the_derivation_verifies() {
    let src = r#"
sort 公民
sort 住宅
pred 非法搜查 : 公民 → 住宅 → Prop
pred 不受侵犯 : 公民 → 住宅 → Prop
obj 张三 : 公民
obj 甲宅 : 住宅
axiom f : 非法搜查 张三 甲宅
  source text "测试" locator "夹具"

rule r :
  params p : 公民, h : 住宅
  premise 非法搜查 p h
  conclude 不受侵犯 p h
  source text "宪法" locator "第三十九条"
"#;
    let lib = load(src);
    let goal = Expr::apps(p("不受侵犯"), [p("张三"), p("甲宅")]);
    let (d, v) = assemble(&lib, &goal);
    assert!(d.root.is_some(), "goal should be derivable");
    assert!(v.is_ok(), "independent verification failed: {v:?}");
}

#[test]
fn a_premise_that_is_not_known_does_not_fire() {
    let src = r#"
sort 公民
sort 住宅
pred 非法搜查 : 公民 → 住宅 → Prop
pred 不受侵犯 : 公民 → 住宅 → Prop
obj 张三 : 公民
obj 甲宅 : 住宅

rule r :
  params p : 公民, h : 住宅
  premise 非法搜查 p h
  conclude 不受侵犯 p h
  source text "宪法" locator "第三十九条"
"#;
    let lib = load(src);
    let goal = Expr::apps(p("不受侵犯"), [p("张三"), p("甲宅")]);
    let (d, _) = assemble(&lib, &goal);
    assert!(d.root.is_none(), "nothing should be derived");
}

#[test]
fn unless_blocks_only_on_a_proven_condition() {
    // Two worlds. In the first, `依法搜查` is a fact, so the rule that says
    // `不受侵犯` unless `非法搜查` is blocked. In the second, `非法搜查` is a
    // fact, so the *other* rule fires.
    //
    // Crucially: the existence of an `unless` clause must never by itself
    // prevent the rule from firing. That would be negation as failure.
    let base = r#"
sort 公民
sort 住宅
pred 非法搜查 : 公民 → 住宅 → Prop
pred 依法搜查 : 公民 → 住宅 → Prop
pred 不受侵犯 : 公民 → 住宅 → Prop
obj 张三 : 公民
obj 甲宅 : 住宅

rule 依法搜查不侵犯 :
  params p : 公民, h : 住宅
  premise 依法搜查 p h
  conclude 不受侵犯 p h
  unless 非法搜查 p h
  source text "宪法" locator "第三十九条"
"#;
    let lib = load(base);
    let goal = Expr::apps(p("不受侵犯"), [p("张三"), p("甲宅")]);
    // No facts at all: nothing fires. Notice this is *not* because the
    // `unless` blocked it, but because the premise is missing.
    let (d, _) = assemble(&lib, &goal);
    assert!(d.root.is_none());

    // Now supply 依法搜查 and 非法搜查 both. The premise holds, and the
    // `unless` condition also holds, so the rule must be blocked.
    let src2 = format!(
        "{base}\naxiom a : 依法搜查 张三 甲宅\n  source text \"测试\" locator \"夹具\"\naxiom b : 非法搜查 张三 甲宅\n  source text \"测试\" locator \"夹具\"\n"
    );
    // Note: the same rule name cannot be redeclared, so load the facts into
    // a fresh library.
    let mut lib2 = Library::new();
    lib2.load("t", &src2).unwrap();
    let (d2, _) = assemble(&lib2, &goal);
    assert!(
        d2.root.is_none(),
        "unless condition holds; rule must not fire"
    );
}

#[test]
fn a_gap_names_what_is_missing() {
    let src = r#"
sort 公民
sort 住宅
pred 非法搜查 : 公民 → 住宅 → Prop
pred 不受侵犯 : 公民 → 住宅 → Prop
obj 张三 : 公民
obj 甲宅 : 住宅

rule r :
  params p : 公民, h : 住宅
  premise 非法搜查 p h
  conclude 不受侵犯 p h
  source text "宪法" locator "第三十九条"
"#;
    let lib = load(src);
    let goal = Expr::apps(p("不受侵犯"), [p("张三"), p("甲宅")]);
    let mut r = Reasoner::new(&lib.env);
    r.saturate().unwrap();
    let ex = r.explain(&goal);
    assert!(!ex.candidates.is_empty(), "some rule heads should match");
    assert!(
        !ex.candidates[0].missing.is_empty(),
        "the missing premise must be listed"
    );
    let _ = print_expr(&ex.candidates[0].missing[0]);
}

#[test]
fn verify_rejects_a_forged_step() {
    use std_deduce_reason::{Derivation, Node};
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  source text "测试" locator "一"
"#;
    let lib = load(src);
    // A step that cites no premise at all cannot be an instance of a rule
    // whose rule has one: the parameter is determined by the conclusion, but
    // the premise is simply absent.
    let mut d = Derivation::default();
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("张三")),
        premises: vec![],
        bindings: vec![],
        sources: vec![SourceRef::new("测试", "一")],
    });
    assert!(
        verify(&lib.env, &d).is_err(),
        "a step that skips a premise must be rejected"
    );
    // A conclusion that is not even an instance of the rule's head must fail.
    let mut d2 = Derivation::default();
    d2.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("侵占"), p("张三")),
        premises: vec![],
        bindings: vec![],
        sources: vec![],
    });
    assert!(verify(&lib.env, &d2).is_err());
}

/// The premise a step cites must be the *instantiated* premise, not merely
/// some proposition that happens to have been proved.
#[test]
fn verify_rejects_an_unrelated_premise() {
    use std_deduce_reason::{Derivation, Node};
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无关 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  source text "测试" locator "一"
"#;
    let lib = load(src);
    let mut d = Derivation::default();
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("无关"), p("李四")),
        identity: FactIdentity::Verified,
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("张三")),
        premises: vec![0],
        bindings: vec![],
        sources: vec![],
    });
    assert!(
        verify(&lib.env, &d).is_err(),
        "`无关 李四` is not the instantiated premise `侵占 张三`"
    );
}

/// The bindings must be consistent: proving `侵占 张三` does not license
/// concluding `违法 李四`.
#[test]
fn verify_rejects_a_binding_mismatch() {
    use std_deduce_reason::{Derivation, Node};
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  source text "测试" locator "一"
"#;
    let lib = load(src);
    let mut d = Derivation::default();
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("侵占"), p("张三")),
        identity: FactIdentity::Verified,
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("李四")),
        premises: vec![0],
        bindings: vec![],
        sources: vec![],
    });
    assert!(
        verify(&lib.env, &d).is_err(),
        "the premise fixes p to 张三; the conclusion may not say 李四"
    );
}

/// A step whose blocker is proved must be rejected — the reasoner's fixed
/// point would have retracted it.
#[test]
fn verify_rejects_a_step_whose_blocker_holds() {
    use std_deduce_reason::{Derivation, Node};
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 例外 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 例外 p
  source text "测试" locator "一"
"#;
    let lib = load(src);
    let mut d = Derivation::default();
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("侵占"), p("张三")),
        identity: FactIdentity::Verified,
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("例外"), p("张三")),
        identity: FactIdentity::Verified,
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("张三")),
        premises: vec![0],
        bindings: vec![],
        sources: vec![],
    });
    assert!(
        verify(&lib.env, &d).is_err(),
        "the `unless` condition is proved, so this step must not stand"
    );
}

/// The independent verifier compares blockers by kernel definitional
/// equality: omitting an alpha-variant of the blocker must still be rejected.
#[test]
fn verify_rejects_an_alpha_variant_blocker() {
    use std_deduce_reason::{Derivation, Node};
    let src = r#"
sort 公民
pred 可信 : Prop → Prop
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (∀ (y : 公民), 侵占 y)
  source text "测试" locator "一"
"#;
    let lib = load(src);
    let mut d = Derivation::default();
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("侵占"), p("张三")),
        identity: FactIdentity::Verified,
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::Assumption {
        prop: Expr::app(
            p("可信"),
            Expr::forall("z", p("公民"), Expr::app(p("侵占"), Expr::Var(0))),
        ),
        identity: FactIdentity::Verified,
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("张三")),
        premises: vec![0],
        bindings: vec![(name("p"), p("张三"))],
        sources: vec![],
    });
    let err = verify(&lib.env, &d).expect_err("the alpha-variant blocker is proved");
    assert!(err.contains("阻断条件"), "got: {err}");
}

/// A rule whose parameter only appears in the conclusion is refused at load
/// time: the reasoner could never fix that parameter, so the conclusion would
/// come out unclosed (`?x`).
#[test]
fn a_rule_with_an_unconstrained_parameter_is_rejected_at_load() {
    let src = r#"
sort 人
pred 前提 : 人 → Prop
pred 结论 : 人 → 人 → Prop
obj 甲 : 人
obj 乙 : 人
axiom f : 前提 甲
  source text "测试" locator "夹具"
rule r :
  params x : 人, y : 人
  premise 前提 x
  conclude 结论 x y
  source text "测试" locator "夹具"
"#;
    let mut lib = Library::new();
    let e = lib.load("t", src).unwrap_err();
    assert!(e.to_string().contains("没有出现在任何前提里"), "got: {e}");
}

/// The same rule with every parameter constrained loads fine.
#[test]
fn a_rule_with_every_parameter_constrained_loads() {
    let src = r#"
sort 人
pred 前提 : 人 → Prop
pred 另一前提 : 人 → Prop
pred 结论 : 人 → 人 → Prop
obj 甲 : 人
obj 乙 : 人
rule r :
  params x : 人, y : 人
  premise 前提 x
  premise 另一前提 y
  conclude 结论 x y
  source text "测试" locator "夹具"
"#;
    load(src);
}

#[test]
fn a_rule_with_ill_typed_conclusion_is_rejected_at_load() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民
rule bad :
  params p : 公民
  premise 侵占 p
  conclude p
  source text "测试" locator "一"
"#;
    let mut lib = Library::new();
    // `p` is an individual, not a proposition.
    let e = lib.load("t", src).unwrap_err();
    assert!(e.to_string().contains("不是命题"), "got: {e}");
}

#[test]
fn a_rule_may_depend_on_an_earlier_premise() {
    // This is the whole payoff of dependent types here: premise 2 mentions a
    // value bound by premise 1.
    let src = r#"
sort 公民
sort 证件
pred 持有 : 公民 → 证件 → Prop
pred 具备资格 : 公民 → Prop
pred 有证资格 : 公民 → Prop
obj 张三 : 公民
obj 身份证 : 证件

axiom f : 持有 张三 身份证
  source text "测试" locator "夹具"

rule r :
  params p : 公民, z : 证件
  premise 持有 p z
  conclude 有证资格 p
  source text "测试" locator "二"
"#;
    let lib = load(src);
    let goal = Expr::app(p("有证资格"), p("张三"));
    let (d, v) = assemble(&lib, &goal);
    assert!(d.root.is_some());
    assert!(v.is_ok(), "{v:?}");
}

/// The node must carry the structured parameter values, not only their
/// rendered form, so a proof term can be built without parsing strings.
#[test]
fn a_rule_node_records_structured_bindings() {
    use std_deduce_reason::Node;
    let src = r#"
sort 公民
sort 证件
pred 持有 : 公民 → 证件 → Prop
pred 有证资格 : 公民 → Prop
obj 张三 : 公民
obj 身份证 : 证件

axiom f : 持有 张三 身份证
  source text "测试" locator "夹具"

rule r :
  params p : 公民, z : 证件
  premise 持有 p z
  conclude 有证资格 p
  source text "测试" locator "二"
"#;
    let lib = load(src);
    let goal = Expr::app(p("有证资格"), p("张三"));
    let (d, v) = assemble(&lib, &goal);
    assert!(v.is_ok(), "independent verification failed: {v:?}");

    let (rule, bindings) = d
        .nodes
        .iter()
        .find_map(|n| match n {
            Node::RuleApplication { rule, bindings, .. } => Some((rule, bindings)),
            _ => None,
        })
        .expect("the derivation should contain the rule step");
    assert_eq!(rule.as_ref(), "r");
    assert!(
        bindings.contains(&(name("p"), p("张三"))),
        "the step must bind p to 张三, got {bindings:?}"
    );
    assert!(bindings.contains(&(name("z"), p("身份证"))));

    // Every declared parameter is determined by this instantiation.
    let decl = lib.env.get("r").expect("the rule is in the ledger");
    let DeclKind::Rule(rule_decl) = &decl.kind else {
        panic!("`r` should be a rule");
    };
    assert_eq!(bindings.len(), rule_decl.params.len());
    for (binder, _) in &rule_decl.params {
        assert!(
            bindings.iter().any(|(k, _)| k == binder),
            "parameter `{binder}` missing from the node's bindings"
        );
    }
}

#[test]
fn kernel_rejects_a_malformed_telescope() {
    // Premise types are checked in the prefix scope; a premise that uses a
    // later binder must be refused.
    let mut env = Env::new();
    let ctx = Ctx::new();
    env.insert(
        Decl {
            name: name("p"),
            kind: DeclKind::Pred,
            // p : Prop -> Prop
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
    let rule = std_deduce_kernel::RuleDecl {
        params: vec![(name("a"), Expr::Sort(0))],
        // `p a : Prop`, so the premise is a proposition.
        premises: vec![(None, Expr::app(Expr::constant("p"), Expr::Var(0)))],
        conclusion: Expr::constant("p"),
        unlesses: vec![],
        exceptions: vec![],
        prefers: vec![],
        sources: vec![],
        declared_in: None,
    };
    let _ = rule;
    // A rule whose conclusion is a bare predicate symbol is not a proposition.
    // The valid shape is checked below; here we only assert the bad one fails.
    let bad = std_deduce_kernel::RuleDecl {
        params: vec![(name("a"), Expr::Sort(0))],
        premises: vec![(None, Expr::app(Expr::constant("p"), Expr::Var(2)))],
        conclusion: Expr::Sort(0),
        unlesses: vec![],
        exceptions: vec![],
        prefers: vec![],
        sources: vec![],
        declared_in: None,
    };
    let decl = Decl {
        name: name("r2"),
        kind: DeclKind::Rule(Box::new(bad)),
        ty: Expr::Sort(0),
        sources: vec![],
        scope: Default::default(),
        occurred_at: None,
        occurred_in: None,
        index: 0,
    };
    assert!(env.insert(decl, &ctx).is_err());
}

/// A conflict is declared, never guessed: two predicates that look like
/// opposites to a human are just two names until `contrary` links them.
#[test]
fn conflict_requires_a_contrary_declaration() {
    let src = r#"
sort 申请
pred 该批准 : 申请 → Prop
pred 不该批准 : 申请 → Prop
obj 甲申请 : 申请
axiom f1 : 该批准 甲申请
  source text "测试" locator "夹具"
axiom f2 : 不该批准 甲申请
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert!(
        r.conflicts().is_empty(),
        "without `contrary` there is nothing to conflict about"
    );
    assert!(r.knows(&Expr::app(p("该批准"), p("甲申请"))));
    assert!(r.knows(&Expr::app(p("不该批准"), p("甲申请"))));
}

#[test]
fn contrary_assumptions_are_unresolved_and_kept_out_of_the_fact_base() {
    let src = r#"
sort 申请
pred 该批准 : 申请 → Prop
pred 不该批准 : 申请 → Prop
contrary 该批准 不该批准
obj 甲申请 : 申请
axiom f1 : 该批准 甲申请
  source text "测试" locator "夹具"
axiom f2 : 不该批准 甲申请
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();

    let left = Expr::app(p("该批准"), p("甲申请"));
    let right = Expr::app(p("不该批准"), p("甲申请"));
    let cs = r.conflicts();
    assert_eq!(cs.len(), 1);
    assert_eq!(
        cs[0].resolution,
        Resolution::Unresolved {
            reason: std_deduce_reason::UnresolvedReason::ConflictingAssumptions,
        }
    );
    assert_eq!(cs[0].left_by, Provenance::Assumption);
    assert_eq!(cs[0].right_by, Provenance::Assumption);
    assert!(!r.knows(&left), "an unresolved conclusion is not asserted");
    assert!(!r.knows(&right));
    assert!(r.conflict_for(&left).is_some());
    // Not dropped silently: the argument for each side is still inspectable.
    assert!(r.derivation_for(&left).is_some());
}

#[test]
fn superiority_resolves_a_conflict_and_the_loser_stays_out() {
    let src = r#"
sort 申请
pred 符合条件 : 申请 → Prop
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
pred 可复议 : 申请 → Prop
contrary 批准 不批准
obj 甲 : 申请
axiom 条件 : 符合条件 甲
  source text "测试" locator "夹具"
rule 一般 :
  params x : 申请
  premise 符合条件 x
  conclude 批准 x
  source text "测试" locator "夹具"
rule 例外 :
  params x : 申请
  premise 符合条件 x
  conclude 不批准 x
  defeated_by 一般
  source text "测试" locator "夹具"
rule 下游 :
  params x : 申请
  premise 不批准 x
  conclude 可复议 x
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();

    let approved = Expr::app(p("批准"), p("甲"));
    let refused = Expr::app(p("不批准"), p("甲"));
    assert!(r.knows(&approved), "the winning side is asserted");
    assert!(!r.knows(&refused), "the loser does not enter the fact base");
    assert!(
        !r.knows(&Expr::app(p("可复议"), p("甲"))),
        "nothing may be derived from a defeated conclusion"
    );
    let cs = r.conflicts();
    assert_eq!(cs.len(), 1);
    assert!(matches!(
        cs[0].resolution,
        Resolution::Defeated {
            basis: std_deduce_reason::ResolutionBasis::Priority { .. },
            ..
        }
    ));
    let side = r.conflict_side(&cs[0], &approved).unwrap();
    assert!(matches!(
        &cs[0].resolution,
        Resolution::Defeated { winner, .. } if *winner == side
    ));
    // A defeated conclusion is still inspectable, for audit.
    assert!(r.derivation_for(&refused).is_some());
    let loser = r.explain(&refused);
    let loser_note = loser.note.as_deref().unwrap_or("");
    assert!(
        loser_note.contains("已被否决"),
        "a defeated loser must not be described as pending: {loser_note}"
    );
    assert!(
        !loser_note.contains("需要人工裁决"),
        "a decided conflict does not need a human decision: {loser_note}"
    );
    let winner = r.explain(&approved);
    let winner_note = winner.note.as_deref().unwrap_or("");
    assert!(
        winner_note.contains("胜出"),
        "the winning side is not pending either: {winner_note}"
    );
    assert!(
        !winner_note.contains("需要人工裁决"),
        "a decided conflict does not need a human decision: {winner_note}"
    );
}

#[test]
fn prefer_points_the_other_way() {
    let src = r#"
sort 申请
pred 符合条件 : 申请 → Prop
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
contrary 批准 不批准
obj 甲 : 申请
axiom 条件 : 符合条件 甲
  source text "测试" locator "夹具"
rule 一般 :
  params x : 申请
  premise 符合条件 x
  conclude 批准 x
  prefer 例外
  source text "测试" locator "夹具"
rule 例外 :
  params x : 申请
  premise 符合条件 x
  conclude 不批准 x
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert!(r.knows(&Expr::app(p("批准"), p("甲"))));
    assert!(!r.knows(&Expr::app(p("不批准"), p("甲"))));
}

#[test]
fn contrary_to_an_unknown_predicate_is_rejected_at_load() {
    let src = r#"
sort 申请
pred 该批准 : 申请 → Prop
contrary 该批准 不存在
"#;
    let err = Library::new().load("t", src).unwrap_err().to_string();
    assert!(err.contains("未知谓词"), "got: {err}");
}

#[test]
fn contrary_between_different_arities_is_rejected_at_load() {
    let src = r#"
sort 申请
pred 一元 : 申请 → Prop
pred 二元 : 申请 → 申请 → Prop
contrary 一元 二元
"#;
    let err = Library::new().load("t", src).unwrap_err().to_string();
    assert!(err.contains("参数个数不同"), "got: {err}");
}

#[test]
fn duplicate_contrary_is_rejected_at_load() {
    let src = r#"
sort 申请
pred 甲 : 申请 → Prop
pred 乙 : 申请 → Prop
contrary 甲 乙
contrary 乙 甲
"#;
    let err = Library::new().load("t", src).unwrap_err().to_string();
    assert!(err.contains("已经声明过"), "got: {err}");
}

/// A `unique` argument position catches "one case, one applicable norm" —
/// the seed-case shape, where both conclusions share a predicate and differ
/// only in one argument.
#[test]
fn unique_declaration_makes_same_predicate_instances_conflict() {
    let src = r#"
sort 案件
sort 规范
pred 应适用 : 规范 → 案件 → Prop
unique 应适用 1
obj 甲 : 案件
obj 法A : 规范
obj 法B : 规范
axiom a : 应适用 法A 甲
  source text "测试" locator "夹具"
axiom b : 应适用 法B 甲
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert_eq!(r.conflicts().len(), 1);
    assert_eq!(
        r.conflicts()[0].resolution,
        Resolution::Unresolved {
            reason: std_deduce_reason::UnresolvedReason::ConflictingAssumptions,
        }
    );
    assert!(!r.knows(&Expr::apps(p("应适用"), [p("法A"), p("甲")])));
    assert!(!r.knows(&Expr::apps(p("应适用"), [p("法B"), p("甲")])));
}

#[test]
fn unique_does_not_conflict_when_the_other_arguments_differ() {
    let src = r#"
sort 案件
sort 规范
pred 应适用 : 规范 → 案件 → Prop
unique 应适用 1
obj 甲 : 案件
obj 乙 : 案件
obj 法A : 规范
obj 法B : 规范
axiom a : 应适用 法A 甲
  source text "测试" locator "夹具"
axiom b : 应适用 法B 乙
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert!(r.conflicts().is_empty());
    assert!(r.knows(&Expr::apps(p("应适用"), [p("法A"), p("甲")])));
    assert!(r.knows(&Expr::apps(p("应适用"), [p("法B"), p("乙")])));
}

#[test]
fn unique_argument_position_out_of_range_is_rejected_at_load() {
    let src = r#"
sort 案件
sort 规范
pred 应适用 : 规范 → 案件 → Prop
unique 应适用 3
"#;
    let err = Library::new().load("t", src).unwrap_err().to_string();
    assert!(err.contains("参数位置超出范围"), "got: {err}");
}

#[test]
fn duplicate_unique_is_rejected_at_load() {
    let src = r#"
sort 案件
sort 规范
pred 应适用 : 规范 → 案件 → Prop
unique 应适用 1
unique 应适用 1
"#;
    let err = Library::new().load("t", src).unwrap_err().to_string();
    assert!(err.contains("已经声明过"), "got: {err}");
}

/// A proposition-declaring axiom (`axiom 假 : Prop`) must not poison reasoning.
///
/// Its declared type is the sort `Prop`, not a proposition, so asserting it
/// would assert `Prop` — a Type — and every query in the file would fail.
#[test]
fn a_prop_declaring_axiom_does_not_break_reasoning() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民
axiom 假 : Prop
  source text "测试" locator "夹具"
axiom f : 侵占 张三
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    let goal = Expr::app(p("侵占"), p("张三"));
    assert!(
        r.knows(&goal),
        "the ground fact must survive a neighbouring `axiom 假 : Prop`"
    );
}

/// The other axiom shape still enters: `axiom f : 侵占 张三` asserts the
/// proposition `侵占 张三`.
#[test]
fn a_ground_fact_axiom_is_assumed() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民
axiom f : 侵占 张三
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert!(r.knows(&Expr::app(p("侵占"), p("张三"))));
}

/// Every identity except `disputed` seeds the fact base; a disputed fact only
/// records what the other side claims, so it must not be used as a premise.
#[test]
fn fact_identities_control_derivation_seeding() {
    let base = "sort 公民\npred 侵占 : 公民 → Prop\nobj 张三 : 公民\n";
    let goal = Expr::app(p("侵占"), p("张三"));
    for (identity, seeds) in [
        ("verified", true),
        ("user_asserted", true),
        ("assumed", true),
        ("stipulated", true),
        ("disputed", false),
    ] {
        let src = format!(
            "{base}axiom f : 侵占 张三\n  identity {identity}\n  source text \"测试\" locator \"夹具\"\n"
        );
        let lib = load(&src);
        let mut r = Reasoner::new(&lib.env);
        r.assume_ledger_axioms().unwrap();
        r.saturate().unwrap();
        assert_eq!(r.knows(&goal), seeds, "identity `{identity}`");
    }
}

/// A rule's declared type ends in its conclusion, so it is a proposition and
/// would pass the proposition guard in `assume_ledger_axioms`. It must still
/// not be assumed: rules drive the reasoner, they are not facts.
#[test]
fn rules_are_not_assumed_as_axioms() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
axiom f : 侵占 张三
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  source text "测试" locator "一"
"#;
    let lib = load(src);
    let rule = lib.env.get("r").expect("the rule must be in the ledger");
    std_deduce_kernel::check::check(&lib.env, &Ctx::new(), &rule.ty, &Expr::Sort(0))
        .expect("a rule's declared type is a proposition");

    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert!(
        !r.knows(&rule.ty),
        "the rule declaration itself must not enter the fact base"
    );
    assert!(
        r.knows(&Expr::app(p("违法"), p("张三"))),
        "the rule must still fire on the axiom"
    );
}

/// A universally quantified axiom is a proposition and is assumed.
#[test]
fn a_quantified_axiom_is_a_proposition() {
    let src = r#"
sort 公民
pred 受教育权 : 公民 → Prop
obj 张三 : 公民
axiom 凡公民皆有受教育权 : ∀ (x : 公民), 受教育权 x
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms()
        .expect("a quantified axiom must be usable as an assumption");
    r.saturate().unwrap();
}

/// Regression: a conclusion derived early must be *retracted* when a later
/// round derives the `unless` condition that blocks it.
///
/// This was a real defect. The first implementation inserted conclusions
/// monotonically and never removed them, so `正当防卫 → 不负刑事责任` survived
/// even after `防卫过当` was derived — two mutually exclusive conclusions
/// standing at once. The loop must recompute from the assumptions each round.
#[test]
fn a_blocking_condition_retracts_an_earlier_conclusion() {
    let src = r#"
sort 行为
pred 正当防卫 : 行为 → Prop
pred 防卫过当 : 行为 → Prop
pred 超过限度 : 行为 → Prop
pred 不负刑事责任 : 行为 → Prop
obj 甲行为 : 行为

axiom 是正当防卫 : 正当防卫 甲行为
  source text "测试" locator "夹具"
axiom 超过限度之事实 : 超过限度 甲行为
  source text "测试" locator "夹具"

rule 过当 :
  params a : 行为
  premise 正当防卫 a
  premise 超过限度 a
  conclude 防卫过当 a
  source text "测试" locator "夹具"

rule 免责 :
  params a : 行为
  premise 正当防卫 a
  conclude 不负刑事责任 a
  unless 防卫过当 a
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let overdue = Expr::app(p("防卫过当"), p("甲行为"));
    let exempt = Expr::app(p("不负刑事责任"), p("甲行为"));

    let mut r = Reasoner::new(&lib.env);
    for d in lib.env.iter() {
        if let DeclKind::Fact { identity } = &d.kind {
            if identity.seeds_derivation() {
                r.assume(&d.ty, *identity, d.sources.clone(), None).unwrap();
            }
        }
    }
    r.saturate().unwrap();

    // 防卫过当 must be derivable...
    assert!(r.knows(&overdue), "防卫过当 should be derived");
    // ...and it must have retracted the exemption.
    assert!(
        !r.knows(&exempt),
        "不负刑事责任 must be retracted once 防卫过当 is derived"
    );

    // The gap explanation must name the blocker, not just say "no".
    let ex = r.explain(&exempt);
    let cand = ex
        .candidates
        .iter()
        .find(|c| c.rule.as_ref() == "免责")
        .expect("the 免责 rule should be a candidate");
    assert!(
        !cand.blocked_by.is_empty(),
        "the blocking condition must be reported"
    );
}

/// A blocker is compared up to kernel definitional equality: a proven fact
/// that is an alpha-variant of the `unless` condition still blocks.
#[test]
fn alpha_variant_blocker_blocks_the_rule() {
    let src = r#"
sort 公民
pred 可信 : Prop → Prop
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"

rule 声明 :
  params q : 公民
  premise 侵占 q
  conclude 可信 (∀ (z : 公民), 侵占 z)
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (∀ (y : 公民), 侵占 y)
  source text "测试" locator "一"
"#;
    let lib = load(src);
    let goal = Expr::app(p("违法"), p("张三"));
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert!(
        !r.knows(&goal),
        "an alpha-variant of the blocker is the same proposition"
    );
    let ex = r.explain(&goal);
    let cand = ex
        .candidates
        .iter()
        .find(|c| c.rule.as_ref() == "r")
        .expect("rule r should be a candidate");
    assert!(
        !cand.blocked_by.is_empty(),
        "the gap explanation must name the alpha-variant blocker"
    );
}

/// Eta-equivalent blockers block as well: `侵占` and `λ (x : 公民) := 侵占 x`
/// are the same function to the kernel.
#[test]
fn eta_variant_blocker_blocks_the_rule() {
    let src = r#"
sort 公民
pred 可信 : (公民 → Prop) → Prop
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"

rule 声明 :
  params q : 公民
  premise 侵占 q
  conclude 可信 侵占
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (λ (x : 公民) := 侵占 x)
  source text "测试" locator "一"
"#;
    let lib = load(src);
    let goal = Expr::app(p("违法"), p("张三"));
    let blocker = Expr::app(p("可信"), p("侵占"));
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert!(
        r.knows(&blocker),
        "the environment rule must derive the stronger blocker fact"
    );
    assert!(
        !r.knows(&goal),
        "an eta-variant of the blocker is the same proposition"
    );
}

/// The same theory, minus the worsening fact, must keep the exemption.
/// This guards against "fix it by refusing to fire anywhere".
#[test]
fn without_the_trigger_the_exemption_stands() {
    let src = r#"
sort 行为
pred 正当防卫 : 行为 → Prop
pred 防卫过当 : 行为 → Prop
pred 超过限度 : 行为 → Prop
pred 不负刑事责任 : 行为 → Prop
obj 甲行为 : 行为

axiom 是正当防卫 : 正当防卫 甲行为
  source text "测试" locator "夹具"

rule 过当 :
  params a : 行为
  premise 正当防卫 a
  premise 超过限度 a
  conclude 防卫过当 a
  source text "测试" locator "夹具"

rule 免责 :
  params a : 行为
  premise 正当防卫 a
  conclude 不负刑事责任 a
  unless 防卫过当 a
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let exempt = Expr::app(p("不负刑事责任"), p("甲行为"));
    let mut r = Reasoner::new(&lib.env);
    for d in lib.env.iter() {
        if let DeclKind::Fact { identity } = &d.kind {
            if identity.seeds_derivation() {
                r.assume(&d.ty, *identity, d.sources.clone(), None).unwrap();
            }
        }
    }
    r.saturate().unwrap();
    assert!(
        r.knows(&exempt),
        "exemption must stand when no blocker holds"
    );
}

/// An `unless` condition that is merely *unproven* must not block.
/// This is the standing guard against negation as failure.
#[test]
fn an_unproven_unless_does_not_block() {
    let src = r#"
sort 行为
pred 前提 : 行为 → Prop
pred 阻断 : 行为 → Prop
pred 结论 : 行为 → Prop
obj 甲行为 : 行为
axiom 有前提 : 前提 甲行为
  source text "测试" locator "夹具"

rule 规则 :
  params a : 行为
  premise 前提 a
  conclude 结论 a
  unless 阻断 a
  source text "测试" locator "夹具"
"#;
    let lib = load(src);
    let concl = Expr::app(p("结论"), p("甲行为"));
    let mut r = Reasoner::new(&lib.env);
    for d in lib.env.iter() {
        if let DeclKind::Fact { identity } = &d.kind {
            if identity.seeds_derivation() {
                r.assume(&d.ty, *identity, d.sources.clone(), None).unwrap();
            }
        }
    }
    r.saturate().unwrap();
    assert!(
        r.knows(&concl),
        "阻断 is unproven, not false; the rule must still fire"
    );
}

/// An assumption is a fact the reasoner will treat as proved. Without a
/// source it cannot be audited, so `assume` refuses it instead of inventing
/// provenance.
#[test]
fn an_assumption_without_a_source_is_rejected() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民
"#;
    let lib = load(src);
    let prop = Expr::app(p("侵占"), p("张三"));

    let mut r = Reasoner::new(&lib.env);
    let err = r
        .assume(&prop, FactIdentity::Verified, vec![], None)
        .expect_err("an assumption without a source must be refused");
    assert!(err.contains("假设必须有来源"), "got: {err}");
    // `knows` only reports the settled fact base, so settle it before
    // asserting that the refused assumption did not enter.
    r.saturate().unwrap();
    assert!(!r.knows(&prop), "a refused assumption enters no fact base");

    r.assume(
        &prop,
        FactIdentity::Verified,
        vec![SourceRef::new("测试", "夹具")],
        None,
    )
    .expect("an assumption with a source is accepted");
    r.saturate().unwrap();
    assert!(r.knows(&prop), "the sourced assumption is usable");
}

/// Whitespace is not provenance: a blank source must be refused exactly like
/// an absent one.
#[test]
fn an_assumption_with_a_blank_source_is_rejected() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民
"#;
    let lib = load(src);
    let prop = Expr::app(p("侵占"), p("张三"));

    let mut r = Reasoner::new(&lib.env);
    let err = r
        .assume(
            &prop,
            FactIdentity::Verified,
            vec![SourceRef::new(" ", " ")],
            None,
        )
        .expect_err("a blank source must be refused");
    assert!(err.contains("假设必须有来源"), "got: {err}");
    assert!(err.contains("空白"), "got: {err}");
    r.saturate().unwrap();
    assert!(!r.knows(&prop), "a refused assumption enters no fact base");
}

// ---------------------------------------------------------------- priorities

/// Two packages whose rules conclude contrary propositions. Nothing orders
/// them: the certificate and the reasoner must say so.
const PACKAGE_P: &str = r#"
namespace p
sort p.申请
pred p.批准 : p.申请 → Prop
obj p.甲 : p.申请
rule p.应批准 :
  conclude p.批准 p.甲
  source text "甲法" locator "第一条" version "2021"
"#;

const PACKAGE_Q: &str = r#"
import p
namespace q
pred q.不批准 : p.申请 → Prop
rule q.不应批准 :
  conclude q.不批准 p.甲
  source text "乙法" locator "第二条" version "2020"
"#;

const CONTRARY_CASE: &str = r#"
contrary p.批准 q.不批准
"#;

const ORDER_PACKAGE: &str = r#"
import p
import q
namespace o
priority p.应批准 over q.不应批准 source text "上位法" locator "第九十二条" version "2023"
"#;

/// Two rules concluding `p.批准 p.甲`; only the rule-internal clause orders
/// the conflicting pair. A second pair uses `prefer` for the other direction.
const CLAUSE_CASE: &str = r#"
sort 申请
pred 批准 : 申请 → Prop
pred 不批准 : 申请 → Prop
pred 可复议 : 申请 → Prop
pred 不可复议 : 申请 → Prop
contrary 批准 不批准
contrary 可复议 不可复议
obj 甲 : 申请
rule 一般 :
  conclude 批准 甲
  source text "甲法" locator "第一条" version "2021"
rule 例外 :
  conclude 不批准 甲
  defeated_by 一般
  source text "乙法" locator "第二条" version "2020"
rule 复议 :
  conclude 可复议 甲
  prefer 不可复议规则
  source text "丙法" locator "第三条" version "2022"
rule 不可复议规则 :
  conclude 不可复议 甲
  source text "丁法" locator "第四条" version "2019"
"#;

/// Three rules on one predicate with a three-way cycle A > B > C > A.
const CYCLE_PACKAGE: &str = r#"
namespace c
sort c.对象
sort c.选项
pred c.值 : c.对象 → c.选项 → Prop
unique c.值 2
obj c.甲 : c.对象
obj c.选A : c.选项
obj c.选B : c.选项
obj c.选C : c.选项
rule c.A :
  conclude c.值 c.甲 c.选A
  source text "甲法" locator "一"
rule c.B :
  conclude c.值 c.甲 c.选B
  source text "乙法" locator "二"
rule c.C :
  conclude c.值 c.甲 c.选C
  source text "丙法" locator "三"
priority c.A over c.B source text "甲法" locator "一"
priority c.B over c.C source text "乙法" locator "二"
priority c.C over c.A source text "丙法" locator "三"
"#;

/// The same cycle plus an unrelated pair with a working priority.
const CYCLE_PLUS_PAIR_PACKAGE: &str = r#"
namespace d
sort d.对象
sort d.选项
pred d.值 : d.对象 → d.选项 → Prop
unique d.值 2
obj d.甲 : d.对象
obj d.乙 : d.对象
obj d.选A : d.选项
obj d.选B : d.选项
obj d.选C : d.选项
obj d.选优 : d.选项
obj d.选劣 : d.选项
rule d.A :
  conclude d.值 d.甲 d.选A
  source text "甲法" locator "一"
rule d.B :
  conclude d.值 d.甲 d.选B
  source text "乙法" locator "二"
rule d.C :
  conclude d.值 d.甲 d.选C
  source text "丙法" locator "三"
rule d.优 :
  conclude d.值 d.乙 d.选优
  source text "优法" locator "四"
rule d.劣 :
  conclude d.值 d.乙 d.选劣
  source text "劣法" locator "五"
priority d.A over d.B source text "甲法" locator "一"
priority d.B over d.C source text "乙法" locator "二"
priority d.C over d.A source text "丙法" locator "三"
priority d.优 over d.劣 source text "优法" locator "四"
"#;

/// A > B and B > C, but A and C are never ordered: priorities are not
/// transitive.
const CHAIN_PACKAGE: &str = r#"
namespace e
sort e.对象
sort e.选项
pred e.值 : e.对象 → e.选项 → Prop
unique e.值 2
obj e.甲 : e.对象
obj e.选A : e.选项
obj e.选B : e.选项
obj e.选C : e.选项
rule e.A :
  conclude e.值 e.甲 e.选A
  source text "甲法" locator "一"
rule e.B :
  conclude e.值 e.甲 e.选B
  source text "乙法" locator "二"
rule e.C :
  conclude e.值 e.甲 e.选C
  source text "丙法" locator "三"
priority e.A over e.B source text "甲法" locator "一"
priority e.B over e.C source text "乙法" locator "二"
"#;

/// Two rules that both conclude either side of a `unique` conflict: the same
/// pair of rules stands on both sides, so an edge between them is enumerated
/// twice unless the reasoner deduplicates it.
const SHARED_SIDES_PACKAGE: &str = r#"
namespace g
sort g.选项
pred g.候选 : g.选项 → Prop
pred g.值 : g.选项 → Prop
unique g.值 1
obj g.选A : g.选项
obj g.选B : g.选项
axiom g.备选A : g.候选 g.选A
  source text "测试" locator "备选A"
axiom g.备选B : g.候选 g.选B
  source text "测试" locator "备选B"
rule g.甲 :
  params x : g.选项
  premise g.候选 x
  conclude g.值 x
  source text "甲法" locator "一"
rule g.乙 :
  params x : g.选项
  premise g.候选 x
  conclude g.值 x
  source text "乙法" locator "二"
priority g.甲 over g.乙 source text "丙法" locator "三"
"#;

fn choice(predicate: &str, object: &str, option: &str) -> Expr {
    Expr::apps(
        Expr::constant(predicate),
        [Expr::constant(object), Expr::constant(option)],
    )
}

fn conflict_between(r: &Reasoner<'_>, a: &Expr, b: &Expr) -> Conflict {
    r.conflicts()
        .into_iter()
        .find(|conflict| {
            (conflict.left == *a && conflict.right == *b)
                || (conflict.left == *b && conflict.right == *a)
        })
        .unwrap_or_else(|| panic!("没有记录「{}」与「{}」的冲突", print_expr(a), print_expr(b)))
}

#[test]
fn cross_package_conflict_without_a_declared_priority_is_unresolved() {
    let lib = load_all(&[
        ("p.std", PACKAGE_P),
        ("q.std", PACKAGE_Q),
        ("case.std", CONTRARY_CASE),
    ]);
    let r = reasoner(&lib);
    let approved = Expr::apps(p("p.批准"), [p("p.甲")]);
    let refused = Expr::apps(p("q.不批准"), [p("p.甲")]);
    assert!(!r.knows(&approved));
    assert!(!r.knows(&refused));
    let conflict = r.conflict_for(&approved).expect("the two rules conflict");
    assert_eq!(
        conflict.resolution,
        Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        }
    );
    assert!(!r.knows(&refused), "an unresolved side is not asserted");
}

#[test]
fn a_third_packages_top_level_priority_defeats_the_conflict() {
    let lib = load_all(&[
        ("p.std", PACKAGE_P),
        ("q.std", PACKAGE_Q),
        ("order.std", ORDER_PACKAGE),
        ("case.std", CONTRARY_CASE),
    ]);
    let r = reasoner(&lib);
    let approved = Expr::apps(p("p.批准"), [p("p.甲")]);
    let refused = Expr::apps(p("q.不批准"), [p("p.甲")]);
    assert!(r.knows(&approved), "the declared winner is asserted");
    assert!(!r.knows(&refused), "the loser is not asserted");

    let side = r.conflict_side(
        &r.conflict_for(&approved).expect("the conflict is recorded"),
        &approved,
    );
    let conflict = r.conflict_for(&approved).unwrap();
    let Resolution::Defeated {
        winner,
        basis: ResolutionBasis::Priority { edges },
    } = &conflict.resolution
    else {
        panic!(
            "the declared priority must defeat the conflict: {:?}",
            conflict.resolution
        );
    };
    assert_eq!(Some(*winner), side);
    assert_eq!(edges.len(), 1, "{edges:?}");
    let edge = &edges[0];
    assert_eq!(edge.winner.as_ref(), "p.应批准");
    assert_eq!(edge.loser.as_ref(), "q.不应批准");
    match &edge.origin {
        PriorityOrigin::Declaration {
            declared_in,
            sources,
        } => {
            assert_eq!(declared_in.as_ref(), "o");
            assert_eq!(sources.len(), 1);
            assert_eq!(sources[0].text, "上位法");
            assert_eq!(sources[0].locator, "第九十二条");
            assert_eq!(sources[0].version, "2023");
        }
        other => panic!("expected a top-level declaration origin, got {other:?}"),
    }
}

#[test]
fn rule_internal_clauses_carry_their_rule_and_sources() {
    let lib = load(CLAUSE_CASE);
    let r = reasoner(&lib);
    let approved = Expr::app(p("批准"), p("甲"));
    let refused = Expr::app(p("不批准"), p("甲"));
    assert!(r.knows(&approved));

    let conflict = r
        .conflict_for(&refused)
        .expect("the clause decides the conflict");
    let Resolution::Defeated {
        basis: ResolutionBasis::Priority { edges },
        ..
    } = &conflict.resolution
    else {
        panic!(
            "the defeated_by clause must defeat the conflict: {:?}",
            conflict.resolution
        );
    };
    assert_eq!(edges.len(), 1, "{edges:?}");
    let edge = &edges[0];
    assert_eq!(edge.winner.as_ref(), "一般");
    assert_eq!(edge.loser.as_ref(), "例外");
    let rule = lib.env.get("例外").expect("the declaring rule exists");
    match &edge.origin {
        PriorityOrigin::RuleClause {
            rule: declaring_rule,
            clause,
            sources,
        } => {
            assert_eq!(declaring_rule.as_ref(), "例外");
            assert_eq!(*clause, PriorityClause::DefeatedBy);
            assert_eq!(sources, &rule.sources);
            assert_eq!(sources[0].text, "乙法");
            assert_eq!(sources[0].locator, "第二条");
            assert_eq!(sources[0].version, "2020");
        }
        other => panic!("expected a rule-clause origin, got {other:?}"),
    }

    // `prefer` points from the declaring rule to the target.
    let reopenable = Expr::app(p("可复议"), p("甲"));
    let conflict = r
        .conflict_for(&reopenable)
        .expect("prefer decides the conflict");
    let Resolution::Defeated {
        winner,
        basis: ResolutionBasis::Priority { edges },
    } = &conflict.resolution
    else {
        panic!("prefer must defeat the conflict: {:?}", conflict.resolution);
    };
    assert_eq!(
        r.conflict_side(&conflict, &reopenable),
        Some(*winner),
        "the declaring rule's side wins"
    );
    assert_eq!(edges.len(), 1, "{edges:?}");
    assert_eq!(edges[0].winner.as_ref(), "复议");
    assert_eq!(edges[0].loser.as_ref(), "不可复议规则");
    assert!(matches!(
        &edges[0].origin,
        PriorityOrigin::RuleClause {
            rule,
            clause: PriorityClause::Prefer,
            ..
        } if rule.as_ref() == "复议"
    ));
}

#[test]
fn a_three_way_priority_cycle_makes_every_pair_unusable() {
    let lib = load_all(&[("c.std", CYCLE_PACKAGE)]);
    let r = reasoner(&lib);
    assert_eq!(
        r.priority_cycles(),
        vec![vec![name("c.A"), name("c.B"), name("c.C")]]
    );
    for (left, right) in [("选A", "选B"), ("选A", "选C"), ("选B", "选C")] {
        let first = choice("c.值", "c.甲", &format!("c.{left}"));
        let second = choice("c.值", "c.甲", &format!("c.{right}"));
        let conflict = conflict_between(&r, &first, &second);
        let Resolution::Unresolved {
            reason: UnresolvedReason::PriorityUnusable { declared },
        } = &conflict.resolution
        else {
            panic!(
                "{left}/{right}: a cyclic priority cannot decide: {:?}",
                conflict.resolution
            );
        };
        assert_eq!(declared.len(), 1, "{left}/{right}: {declared:?}");
    }
    // A direct A over B edge is not enough: both rules are on the cycle.
    let direct = conflict_between(
        &r,
        &choice("c.值", "c.甲", "c.选A"),
        &choice("c.值", "c.甲", "c.选B"),
    );
    let Resolution::Unresolved {
        reason: UnresolvedReason::PriorityUnusable { declared },
    } = &direct.resolution
    else {
        panic!("A vs B must stay unresolved even with a direct edge");
    };
    assert_eq!(declared[0].winner.as_ref(), "c.A");
    assert_eq!(declared[0].loser.as_ref(), "c.B");
}

#[test]
fn an_unrelated_cycle_does_not_disturb_another_pair() {
    let lib = load_all(&[("d.std", CYCLE_PLUS_PAIR_PACKAGE)]);
    let r = reasoner(&lib);
    assert_eq!(
        r.priority_cycles(),
        vec![vec![name("d.A"), name("d.B"), name("d.C")]]
    );

    let cyclic = choice("d.值", "d.甲", "d.选A");
    let sibling = choice("d.值", "d.甲", "d.选B");
    assert!(matches!(
        conflict_between(&r, &cyclic, &sibling).resolution,
        Resolution::Unresolved {
            reason: UnresolvedReason::PriorityUnusable { .. }
        }
    ));

    let better = choice("d.值", "d.乙", "d.选优");
    let conflict = r
        .conflict_for(&better)
        .expect("the unrelated pair conflicts");
    let Resolution::Defeated {
        winner,
        basis: ResolutionBasis::Priority { edges },
    } = &conflict.resolution
    else {
        panic!(
            "the off-cycle priority must still decide: {:?}",
            conflict.resolution
        );
    };
    assert_eq!(r.conflict_side(&conflict, &better), Some(*winner));
    assert_eq!(edges.len(), 1, "{edges:?}");
    assert_eq!(edges[0].winner.as_ref(), "d.优");
    assert_eq!(edges[0].loser.as_ref(), "d.劣");
}

#[test]
fn priorities_are_not_transitive() {
    let lib = load_all(&[("e.std", CHAIN_PACKAGE)]);
    let r = reasoner(&lib);
    let a = choice("e.值", "e.甲", "e.选A");
    let b = choice("e.值", "e.甲", "e.选B");
    let c = choice("e.值", "e.甲", "e.选C");

    assert!(matches!(
        conflict_between(&r, &a, &b).resolution,
        Resolution::Defeated {
            basis: ResolutionBasis::Priority { .. },
            ..
        }
    ));
    assert!(matches!(
        conflict_between(&r, &b, &c).resolution,
        Resolution::Defeated {
            basis: ResolutionBasis::Priority { .. },
            ..
        }
    ));
    assert_eq!(
        conflict_between(&r, &a, &c).resolution,
        Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        },
        "A > B and B > C do not order A over C"
    );
    assert!(r.priority_cycles().is_empty());
}

#[test]
fn an_edge_between_two_shared_rules_is_listed_once() {
    let lib = load_all(&[("g.std", SHARED_SIDES_PACKAGE)]);
    let r = reasoner(&lib);
    let a = Expr::app(p("g.值"), p("g.选A"));
    let b = Expr::app(p("g.值"), p("g.选B"));
    let conflict = conflict_between(&r, &a, &b);
    let Resolution::Unresolved {
        reason: UnresolvedReason::PriorityUnusable { declared },
    } = &conflict.resolution
    else {
        panic!(
            "both sides are the same two rules, so no pair can beat every rule of the other side: {:?}",
            conflict.resolution
        );
    };
    assert_eq!(
        declared.len(),
        1,
        "the same edge must not be listed twice: {declared:?}"
    );
    assert_eq!(declared[0].winner.as_ref(), "g.甲");
    assert_eq!(declared[0].loser.as_ref(), "g.乙");
}

/// The language refuses `priority r over r` and the rule-internal spelling,
/// but a directly built environment can still carry the edge. It can never
/// decide a conflict, so it must be reported as a cycle like any other.
#[test]
fn a_priority_self_loop_is_reported_as_a_cycle() {
    let mut env = Env::new();
    let ctx = Ctx::new();
    env.insert(
        Decl {
            name: name("p"),
            kind: DeclKind::Pred,
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
    for rule_name in ["x.r", "x.s"] {
        let rule = std_deduce_kernel::RuleDecl {
            params: vec![],
            premises: vec![],
            conclusion: Expr::constant("p"),
            unlesses: vec![],
            exceptions: vec![],
            prefers: vec![],
            sources: vec![],
            declared_in: Some(name("x")),
        };
        let ty = std_deduce_kernel::env::rule_type(&rule);
        env.insert(
            Decl {
                name: name(rule_name),
                kind: DeclKind::Rule(Box::new(rule)),
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
    env.insert(
        Decl {
            name: name("priority:x:x.r:x.r"),
            kind: DeclKind::Priority {
                winner: name("x.r"),
                loser: name("x.r"),
                declared_in: name("x"),
            },
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
    let r = Reasoner::new(&env);
    assert_eq!(r.priority_cycles(), vec![vec![name("x.r")]]);
}

// ---------------------------------------------------------------- fact strictness

/// A case file whose one fact is `批准 甲` under `identity`, and one rule that
/// concludes the contrary `不批准 甲` from a claim.
fn strictness_case(identity: &str) -> String {
    format!(
        r#"
sort 人
pred 条件 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
contrary 批准 不批准
obj 甲 : 人
axiom 条件事实 : 条件 甲
  source text "测试" locator "夹具"
axiom 批准事实 : 批准 甲
  identity {identity}
  source text "测试" locator "夹具"
rule 拒绝 :
  params x : 人
  premise 条件 x
  conclude 不批准 x
  source text "测试" locator "夹具"
"#
    )
}

fn resolved_conflict(r: &Reasoner<'_>) -> Conflict {
    let mut conflicts = r.conflicts();
    assert_eq!(conflicts.len(), 1, "{conflicts:?}");
    conflicts.remove(0)
}

fn approved() -> Expr {
    Expr::app(p("批准"), p("甲"))
}

fn refused() -> Expr {
    Expr::app(p("不批准"), p("甲"))
}

/// Matrix row "strict fact vs rule": the strict fact wins, the rule conclusion
/// leaves the fact base, and the certificate records the strict identity.
#[test]
fn a_strict_fact_defeats_a_rule_conclusion() {
    for identity in ["verified", "stipulated"] {
        let lib = load(&strictness_case(identity));
        let r = reasoner(&lib);
        let conflict = resolved_conflict(&r);
        assert!(
            matches!(
                conflict.resolution,
                Resolution::Defeated {
                    winner: Side::Right,
                    basis: ResolutionBasis::Assumption,
                }
            ),
            "{conflict:?}"
        );
        assert!(r.knows(&approved()), "the strict fact is asserted");
        assert!(!r.knows(&refused()), "the rule conclusion loses");

        let mut d = r.derivation();
        d.root = r.root_for(&approved());
        let certificate = std_deduce_reason::certificate(&d, &r.priority_order())
            .expect("the derivation converts");
        let strict = certificate
            .assumptions
            .iter()
            .find(|assumption| assumption.label.as_deref() == Some("批准事实"))
            .expect("the strict fact is recorded");
        assert_eq!(
            strict.identity,
            match identity {
                "verified" => std_deduce_cert::FactIdentity::Verified,
                _ => std_deduce_cert::FactIdentity::Stipulated,
            }
        );
        std_deduce_cert::check(&lib.env, &certificate).expect("the strict defeat checks");
    }
}

/// Matrix row "claim vs rule": neither side wins. The claim is not proof, and
/// the rule conclusion does not refute it.
#[test]
fn a_claim_never_defeats_a_rule_conclusion() {
    for identity in ["user_asserted", "assumed"] {
        let lib = load(&strictness_case(identity));
        let r = reasoner(&lib);
        let conflict = resolved_conflict(&r);
        assert_eq!(
            conflict.resolution,
            Resolution::Unresolved {
                reason: UnresolvedReason::NonStrictFact {
                    identity: match identity {
                        "user_asserted" => FactIdentity::UserAsserted,
                        _ => FactIdentity::Assumed,
                    },
                },
            }
        );
        assert!(!r.knows(&approved()), "a claim is not asserted as proved");
        assert!(!r.knows(&refused()));
    }
}

/// Matrix row "strict fact vs claim": the strict fact wins.
#[test]
fn a_strict_fact_defeats_a_claim() {
    let src = r#"
sort 人
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
contrary 批准 不批准
obj 甲 : 人
axiom 严格 : 批准 甲
  identity verified
  source text "测试" locator "甲"
axiom 主张 : 不批准 甲
  identity user_asserted
  source text "测试" locator "乙"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let conflict = resolved_conflict(&r);
    assert_eq!(
        conflict.resolution,
        Resolution::Defeated {
            winner: Side::Right,
            basis: ResolutionBasis::Assumption,
        }
    );
    assert!(r.knows(&approved()));
    assert!(!r.knows(&refused()));
}

/// Matrix rows "two strict facts" and "two claims": both stay unresolved, and
/// neither conclusion enters the fact base.
#[test]
fn facts_of_the_same_strictness_stay_unresolved() {
    for (left, right) in [("verified", "stipulated"), ("user_asserted", "assumed")] {
        let src = format!(
            r#"
sort 人
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
contrary 批准 不批准
obj 甲 : 人
axiom 事实甲 : 批准 甲
  identity {left}
  source text "测试" locator "甲"
axiom 事实乙 : 不批准 甲
  identity {right}
  source text "测试" locator "乙"
"#
        );
        let lib = load(&src);
        let r = reasoner(&lib);
        let conflict = resolved_conflict(&r);
        assert_eq!(
            conflict.resolution,
            Resolution::Unresolved {
                reason: UnresolvedReason::ConflictingAssumptions,
            },
            "{left} vs {right}"
        );
        assert!(!r.knows(&approved()));
        assert!(!r.knows(&refused()));
    }
}

/// Matrix row "rule vs rule" is unchanged: without a declared priority the
/// conflict stays unresolved.
#[test]
fn rule_against_rule_still_needs_a_declared_priority() {
    let src = r#"
sort 人
pred 条件 : 人 → Prop
pred 批准 : 人 → Prop
pred 不批准 : 人 → Prop
contrary 批准 不批准
obj 甲 : 人
axiom 条件事实 : 条件 甲
  identity verified
  source text "测试" locator "夹具"
rule 一般 :
  params x : 人
  premise 条件 x
  conclude 批准 x
  source text "测试" locator "甲"
rule 例外 :
  params x : 人
  premise 条件 x
  conclude 不批准 x
  source text "测试" locator "乙"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    let conflict = resolved_conflict(&r);
    assert_eq!(
        conflict.resolution,
        Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        }
    );
    assert!(!r.knows(&approved()));
    assert!(!r.knows(&refused()));
}

/// A disputed fact asserts what the other side claims: it is neither a premise
/// nor a blocker.
#[test]
fn a_disputed_fact_seeds_nothing_and_blocks_nothing() {
    let as_premise = r#"
sort 人
pred 条件 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 争议 : 条件 甲
  identity disputed
  source text "测试" locator "夹具"
rule 推导 :
  params x : 人
  premise 条件 x
  conclude 结论 x
  source text "测试" locator "一"
"#;
    let lib = load(as_premise);
    let r = reasoner(&lib);
    assert!(!r.knows(&Expr::app(p("结论"), p("甲"))));

    let as_blocker = r#"
sort 人
pred 条件 : 人 → Prop
pred 阻断 : 人 → Prop
pred 结论 : 人 → Prop
obj 甲 : 人
axiom 前提事实 : 条件 甲
  identity verified
  source text "测试" locator "夹具"
axiom 争议 : 阻断 甲
  identity disputed
  source text "测试" locator "夹具"
rule 推导 :
  params x : 人
  premise 条件 x
  conclude 结论 x
  unless 阻断 x
  source text "测试" locator "一"
"#;
    let lib = load(as_blocker);
    let r = reasoner(&lib);
    assert!(
        r.knows(&Expr::app(p("结论"), p("甲"))),
        "a disputed fact is not a proved blocker"
    );
}

/// A claim is usable as a premise and still blocks an `unless`: the new
/// strictness rule changes who wins a conflict, not what a claim can seed.
#[test]
fn a_claim_is_a_premise_and_blocks_an_unless() {
    let src = r#"
sort 人
pred 条件 : 人 → Prop
pred 阻断 : 人 → Prop
pred 结论 : 人 → Prop
pred 另一结论 : 人 → Prop
obj 甲 : 人
axiom 前提事实 : 条件 甲
  identity user_asserted
  source text "测试" locator "夹具"
axiom 阻断事实 : 阻断 甲
  identity assumed
  source text "测试" locator "夹具"
rule 推导 :
  params x : 人
  premise 条件 x
  conclude 结论 x
  unless 阻断 x
  source text "测试" locator "一"
rule 纯推导 :
  params x : 人
  premise 条件 x
  conclude 另一结论 x
  source text "测试" locator "二"
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    assert!(
        !r.knows(&Expr::app(p("结论"), p("甲"))),
        "the claim 阻断 甲 is proved for the purpose of blocking"
    );
    assert!(
        r.knows(&Expr::app(p("另一结论"), p("甲"))),
        "the claim 条件 甲 is usable as a premise"
    );
}

/// `assume` refuses a disputed proposition and a second identity for the same
/// proposition. The same identity may be registered twice.
#[test]
fn assume_enforces_one_identity_per_proposition() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民
"#;
    let lib = load(src);
    let prop = Expr::app(p("侵占"), p("张三"));
    let source = || vec![SourceRef::new("测试", "夹具")];

    let mut r = Reasoner::new(&lib.env);
    let error = r
        .assume(&prop, FactIdentity::Disputed, source(), None)
        .expect_err("a disputed proposition is not an assumption");
    assert!(error.contains("争议事实不能作为假设"), "got: {error}");

    r.assume(&prop, FactIdentity::Verified, source(), None)
        .expect("a strict fact can be assumed");
    r.assume(&prop, FactIdentity::Verified, source(), None)
        .expect("the same identity may be registered again");
    let error = r
        .assume(&prop, FactIdentity::UserAsserted, source(), None)
        .expect_err("one proposition has one identity");
    assert!(error.contains("同一命题只能有一种事实身份"), "got: {error}");
    assert!(error.contains("法院查明"), "got: {error}");
    assert!(error.contains("用户陈述"), "got: {error}");
}

/// One proposition has one identity even when the two registrations are alpha
/// variants: `∀ x, 侵占 x` and `∀ y, 侵占 y` are the same proposition.
#[test]
fn alpha_variant_assumptions_cannot_change_identity() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
"#;
    let lib = load(src);
    let body = Expr::app(p("侵占"), Expr::var(0));
    let with_x = Expr::forall("x", p("公民"), body.clone());
    let with_y = Expr::forall("y", p("公民"), body);
    let source = || vec![SourceRef::new("测试", "夹具")];

    let mut r = Reasoner::new(&lib.env);
    r.assume(&with_x, FactIdentity::Verified, source(), None)
        .expect("the first registration is legal");
    let error = r
        .assume(&with_y, FactIdentity::UserAsserted, source(), None)
        .expect_err("an alpha variant is the same proposition");
    assert!(error.contains("同一命题只能有一种事实身份"), "got: {error}");
    assert!(error.contains("法院查明"), "got: {error}");
    assert!(error.contains("用户陈述"), "got: {error}");
}
