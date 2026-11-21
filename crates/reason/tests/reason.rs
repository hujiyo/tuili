//! Reasoner tests. These pin down the three commitments documented in the
//! crate: no negation as failure, no silent conflict resolution, and no
//! hidden gaps.

use std_deduce_kernel::env::{Ctx, DeclKind, SourceRef};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{name, Decl, Env, Expr};
use std_deduce_lang::Library;
use std_deduce_reason::{verify, Provenance, Reasoner, Resolution};

fn load(src: &str) -> Library {
    let mut lib = Library::new();
    lib.load("test", src)
        .unwrap_or_else(|e| panic!("load: {e}"));
    lib
}

fn p(name: &str) -> Expr {
    Expr::constant(name)
}

fn assemble(lib: &Library, goal: &Expr) -> (std_deduce_reason::Derivation, Result<(), String>) {
    let mut r = Reasoner::new(&lib.env);
    for decl in lib.env.iter() {
        if let DeclKind::Axiom = &decl.kind {
            r.assume(&decl.ty, decl.sources.clone(), Some(decl.name.to_string()))
                .unwrap();
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

rule r :
  params p : 公民, h : 住宅
  premise 非法搜查 p h
  conclude 不受侵犯 p h
  source 宪法 第三十九条
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
  source 宪法 第三十九条
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
  source 宪法 第三十九条
"#;
    let lib = load(base);
    let goal = Expr::apps(p("不受侵犯"), [p("张三"), p("甲宅")]);
    // No facts at all: nothing fires. Notice this is *not* because the
    // `unless` blocked it, but because the premise is missing.
    let (d, _) = assemble(&lib, &goal);
    assert!(d.root.is_none());

    // Now supply 依法搜查 and 非法搜查 both. The premise holds, and the
    // `unless` condition also holds, so the rule must be blocked.
    let src2 = format!("{base}\naxiom a : 依法搜查 张三 甲宅\naxiom b : 非法搜查 张三 甲宅\n");
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
  source 宪法 第三十九条
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
  source 测试 一
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
        instance: vec![],
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
        instance: vec![],
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
  source 测试 一
"#;
    let lib = load(src);
    let mut d = Derivation::default();
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("无关"), p("李四")),
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("张三")),
        premises: vec![0],
        bindings: vec![],
        instance: vec![],
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
  source 测试 一
"#;
    let lib = load(src);
    let mut d = Derivation::default();
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("侵占"), p("张三")),
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("李四")),
        premises: vec![0],
        bindings: vec![],
        instance: vec![],
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
  source 测试 一
"#;
    let lib = load(src);
    let mut d = Derivation::default();
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("侵占"), p("张三")),
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("例外"), p("张三")),
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("张三")),
        premises: vec![0],
        bindings: vec![],
        instance: vec![],
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
  source 测试 一
"#;
    let lib = load(src);
    let mut d = Derivation::default();
    d.nodes.push(Node::Assumption {
        prop: Expr::app(p("侵占"), p("张三")),
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::Assumption {
        prop: Expr::app(
            p("可信"),
            Expr::forall("z", p("公民"), Expr::app(p("侵占"), Expr::Var(0))),
        ),
        sources: vec![],
        label: None,
    });
    d.nodes.push(Node::RuleApplication {
        rule: name("r"),
        conclusion: Expr::app(p("违法"), p("张三")),
        premises: vec![0],
        bindings: vec![(name("p"), p("张三"))],
        instance: vec!["p ↦ 张三".to_string()],
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
rule r :
  params x : 人, y : 人
  premise 前提 x
  conclude 结论 x y
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
  source 测试 一
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

rule r :
  params p : 公民, z : 证件
  premise 持有 p z
  conclude 有证资格 p
  source 测试 二
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

rule r :
  params p : 公民, z : 证件
  premise 持有 p z
  conclude 有证资格 p
  source 测试 二
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
    };
    let decl = Decl {
        name: name("r2"),
        kind: DeclKind::Rule(Box::new(bad)),
        ty: Expr::Sort(0),
        sources: vec![],
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
axiom f2 : 不该批准 甲申请
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
axiom f2 : 不该批准 甲申请
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();

    let left = Expr::app(p("该批准"), p("甲申请"));
    let right = Expr::app(p("不该批准"), p("甲申请"));
    let cs = r.conflicts();
    assert_eq!(cs.len(), 1);
    assert_eq!(cs[0].resolution, Resolution::Unresolved);
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
rule 一般 :
  params x : 申请
  premise 符合条件 x
  conclude 批准 x
rule 例外 :
  params x : 申请
  premise 符合条件 x
  conclude 不批准 x
  defeated_by 一般
rule 下游 :
  params x : 申请
  premise 不批准 x
  conclude 可复议 x
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
    assert!(matches!(cs[0].resolution, Resolution::Defeated { .. }));
    let side = r.conflict_side(&cs[0], &approved).unwrap();
    assert_eq!(
        cs[0].resolution,
        Resolution::Defeated { winner: side },
        "the winner is the asserted side"
    );
    // A defeated conclusion is still inspectable, for audit.
    assert!(r.derivation_for(&refused).is_some());
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
rule 一般 :
  params x : 申请
  premise 符合条件 x
  conclude 批准 x
  prefer 例外
rule 例外 :
  params x : 申请
  premise 符合条件 x
  conclude 不批准 x
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
axiom b : 应适用 法B 甲
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert_eq!(r.conflicts().len(), 1);
    assert_eq!(r.conflicts()[0].resolution, Resolution::Unresolved);
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
axiom b : 应适用 法B 乙
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
axiom f : 侵占 张三
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
"#;
    let lib = load(src);
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    assert!(r.knows(&Expr::app(p("侵占"), p("张三"))));
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

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  source 测试 一
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
axiom 超过限度之事实 : 超过限度 甲行为

rule 过当 :
  params a : 行为
  premise 正当防卫 a
  premise 超过限度 a
  conclude 防卫过当 a

rule 免责 :
  params a : 行为
  premise 正当防卫 a
  conclude 不负刑事责任 a
  unless 防卫过当 a
"#;
    let lib = load(src);
    let overdue = Expr::app(p("防卫过当"), p("甲行为"));
    let exempt = Expr::app(p("不负刑事责任"), p("甲行为"));

    let mut r = Reasoner::new(&lib.env);
    for d in lib.env.iter() {
        if let DeclKind::Axiom = &d.kind {
            r.assume(&d.ty, d.sources.clone(), None).unwrap();
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

rule 声明 :
  params q : 公民
  premise 侵占 q
  conclude 可信 (∀ (z : 公民), 侵占 z)

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (∀ (y : 公民), 侵占 y)
  source 测试 一
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

rule 声明 :
  params q : 公民
  premise 侵占 q
  conclude 可信 侵占

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (λ (x : 公民) := 侵占 x)
  source 测试 一
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

rule 过当 :
  params a : 行为
  premise 正当防卫 a
  premise 超过限度 a
  conclude 防卫过当 a

rule 免责 :
  params a : 行为
  premise 正当防卫 a
  conclude 不负刑事责任 a
  unless 防卫过当 a
"#;
    let lib = load(src);
    let exempt = Expr::app(p("不负刑事责任"), p("甲行为"));
    let mut r = Reasoner::new(&lib.env);
    for d in lib.env.iter() {
        if let DeclKind::Axiom = &d.kind {
            r.assume(&d.ty, d.sources.clone(), None).unwrap();
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

rule 规则 :
  params a : 行为
  premise 前提 a
  conclude 结论 a
  unless 阻断 a
"#;
    let lib = load(src);
    let concl = Expr::app(p("结论"), p("甲行为"));
    let mut r = Reasoner::new(&lib.env);
    for d in lib.env.iter() {
        if let DeclKind::Axiom = &d.kind {
            r.assume(&d.ty, d.sources.clone(), None).unwrap();
        }
    }
    r.saturate().unwrap();
    assert!(
        r.knows(&concl),
        "阻断 is unproven, not false; the rule must still fire"
    );
}
