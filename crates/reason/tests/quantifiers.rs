//! Universal elimination: on-demand instantiation of `∀ (x : T), P x` facts.
//!
//! The reasoner never enumerates objects. A closed goal or a closed rule
//! premise supplies the value of every binding variable, and the instance is
//! a derived fact recorded as an `axiom_instance` node.

use std_deduce_kernel::term::is_closed;
use std_deduce_kernel::{Expr, Name};
use std_deduce_lang::Library;
use std_deduce_reason::{verify, Node, Reasoner};

fn load(src: &str) -> Library {
    let mut lib = Library::new();
    lib.load("test", src)
        .unwrap_or_else(|e| panic!("load: {e}"));
    lib
}

fn atom(function: &str, argument: &str) -> Expr {
    Expr::app(Expr::constant(function), Expr::constant(argument))
}

fn reasoner(lib: &Library) -> Reasoner<'_> {
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r
}

const CITIZEN: &str = r#"
sort 公民
pred 受教育权利 : 公民 → Prop
axiom 凡公民皆有受教育权 : ∀ (p : 公民), 受教育权利 p
  source text "示例法" locator "第一条"
obj 张三 : 公民
"#;

const RELATION: &str = r#"
sort 人
pred 关系 : 人 → 人 → Prop
axiom 人人有关系 : ∀ (x : 人), ∀ (y : 人), 关系 x y
  source text "示例法" locator "第一条"
obj 甲 : 人
obj 乙 : 人
"#;

#[test]
fn demand_instantiates_a_universal_fact_for_the_goal() {
    let lib = load(CITIZEN);
    let goal = Expr::app(Expr::constant("受教育权利"), Expr::constant("张三"));
    let mut r = reasoner(&lib);
    let instance = r
        .demand(&goal)
        .expect("demand runs")
        .expect("the universal fact produces an instance");
    assert_eq!(instance.axiom.as_ref(), "凡公民皆有受教育权");
    assert_eq!(instance.bindings.len(), 1);
    assert_eq!(instance.bindings[0].0.as_ref(), "p");
    assert_eq!(instance.bindings[0].1, Expr::constant("张三"));
    assert!(is_closed(&instance.conclusion));

    r.saturate().expect("the demanded instance saturates");
    assert!(r.knows(&goal), "the instance proves the goal");
    let root = r.root_for(&goal).expect("the goal has a node");
    let Node::AxiomInstance {
        axiom, conclusion, ..
    } = &r.derivation().nodes[root]
    else {
        panic!("the goal's node must be the universal instance");
    };
    assert_eq!(axiom.as_ref(), "凡公民皆有受教育权");
    assert_eq!(conclusion, &instance.conclusion);
    // The internal checker rebuilds the step from the kernel declaration.
    let mut derivation = r.derivation();
    derivation.root = Some(root);
    verify(&lib.env, &derivation).expect("the instance step verifies");
}

#[test]
fn a_two_binder_universal_instantiates_outermost_first() {
    let lib = load(RELATION);
    let goal = Expr::apps(
        Expr::constant("关系"),
        [Expr::constant("甲"), Expr::constant("乙")],
    );
    let mut r = reasoner(&lib);
    let instance = r.demand(&goal).unwrap().expect("an instance exists");
    assert_eq!(
        instance.bindings,
        vec![
            (Name::from("x"), Expr::constant("甲")),
            (Name::from("y"), Expr::constant("乙")),
        ],
        "bindings are recorded in the declaration's binder order"
    );
    assert!(is_closed(&instance.conclusion));
    r.saturate().unwrap();
    assert!(r.knows(&goal));
}

#[test]
fn a_repeated_binder_must_meet_the_same_term() {
    let src = r#"
sort 人
pred 同龄 : 人 → 人 → Prop
axiom 自己同龄 : ∀ (x : 人), 同龄 x x
  source text "示例法" locator "第一条"
obj 甲 : 人
obj 乙 : 人
"#;
    let lib = load(src);
    let r = reasoner(&lib);
    // The repeated binder forces the two arguments to be identical.
    let unequal = Expr::apps(
        Expr::constant("同龄"),
        [Expr::constant("甲"), Expr::constant("乙")],
    );
    assert!(
        r.demand(&unequal).unwrap().is_none(),
        "`同龄 x x` has no instance at `同龄 甲 乙`"
    );
    let diagonal = Expr::apps(
        Expr::constant("同龄"),
        [Expr::constant("甲"), Expr::constant("甲")],
    );
    assert!(
        r.demand(&diagonal).unwrap().is_some(),
        "a diagonal instance exists"
    );
}

#[test]
fn an_arrow_shaped_universal_is_not_instantiated() {
    // `∀ p, p → p` is a universal proposition whose body is an implication,
    // not a predicate atom. The task deliberately does not implement higher
    // order instantiation, so this is not a candidate.
    let src = r#"
pred 晴朗 : Prop
axiom 恒等定理 : ∀ (p : Prop), p → p
  source text "示例" locator "逻辑"
"#;
    let lib = load(src);
    let goal = Expr::pi(Expr::constant("晴朗"), Expr::constant("晴朗"));
    let r = reasoner(&lib);
    assert!(
        r.demand(&goal).unwrap().is_none(),
        "an implication body is outside the implemented instantiation"
    );
}

#[test]
fn a_disputed_universal_is_not_an_instantiation_source() {
    let src = r#"
sort 公民
pred 受教育权利 : 公民 → Prop
axiom 凡公民皆有受教育权 : ∀ (p : 公民), 受教育权利 p
  identity disputed
  source text "对方主张" locator "第一段"
obj 张三 : 公民
"#;
    let lib = load(src);
    let goal = atom("受教育权利", "张三");
    let r = reasoner(&lib);
    assert!(
        r.demand(&goal).unwrap().is_none(),
        "a disputed fact asserts only what the other side claims, so it cannot be instantiated"
    );
}

#[test]
fn the_first_universal_in_name_order_wins() {
    let src = r#"
sort 公民
pred 受教育权利 : 公民 → Prop
axiom 一 : ∀ (p : 公民), 受教育权利 p
  source text "示例法" locator "第一条"
axiom 二 : ∀ (p : 公民), 受教育权利 p
  source text "示例法" locator "第二条"
obj 张三 : 公民
"#;
    let lib = load(src);
    let goal = atom("受教育权利", "张三");
    let r = reasoner(&lib);
    let instance = r.demand(&goal).unwrap().expect("an instance exists");
    assert_eq!(
        instance.axiom.as_ref(),
        "一",
        "candidates are tried in axiom-name order"
    );
}

#[test]
fn a_premise_driven_instance_lets_a_rule_fire() {
    let src = r#"
sort 公民
pred 受教育权利 : 公民 → Prop
def 教育权 : 公民 → Prop := 受教育权利
pred 登记在册 : 公民 → Prop
pred 获得保障 : 公民 → Prop
axiom 凡公民皆有受教育权 : ∀ (p : 公民), 受教育权利 p
  source text "示例法" locator "第一条"
obj 张三 : 公民
axiom 张三登记在册 : 登记在册 张三
  source text "案件材料" locator "第一页"
rule 教育保障 :
  params p : 公民
  premise 登记在册 p
  premise 教育权 p
  conclude 获得保障 p
  source text "测试法" locator "第一条"
"#;
    let lib = load(src);
    let mut r = reasoner(&lib);
    // No goal is demanded: the closed second premise of the rule drives the
    // instantiation during saturation.
    r.saturate().unwrap();
    let goal = atom("获得保障", "张三");
    assert!(r.knows(&goal), "the rule fires on the universal instance");
    let derivation = r.derivation();
    verify(&lib.env, &derivation).expect("every step verifies");
    let instances: Vec<&Node> = derivation
        .nodes
        .iter()
        .filter(|node| matches!(node, Node::AxiomInstance { .. }))
        .collect();
    assert_eq!(instances.len(), 1, "exactly one instance is derived");
    assert!(
        derivation.nodes.iter().any(|node| matches!(
            node,
            Node::RuleApplication { rule, .. } if rule.as_ref() == "教育保障"
        )),
        "the rule is recorded"
    );
}

#[test]
fn a_removed_instance_does_not_satisfy_a_premise() {
    // A strict fact contradicts the universal instance's conclusion. The
    // instance losses the conflict and leaves the premise missing: a removed
    // conclusion must never be used as a premise.
    let src = r#"
sort 公民
pred 受教育权利 : 公民 → Prop
pred 非受教育权利 : 公民 → Prop
contrary 受教育权利 非受教育权利
pred 登记在册 : 公民 → Prop
pred 获得保障 : 公民 → Prop
axiom 凡公民皆有受教育权 : ∀ (p : 公民), 受教育权利 p
  source text "示例法" locator "第一条"
obj 张三 : 公民
axiom 张三登记在册 : 登记在册 张三
  source text "案件材料" locator "第一页"
axiom 张三无权 : 非受教育权利 张三
  identity verified
  source text "判决书" locator "查明"
rule 教育保障 :
  params p : 公民
  premise 登记在册 p
  premise 受教育权利 p
  conclude 获得保障 p
  source text "测试法" locator "第一条"
"#;
    let lib = load(src);
    let mut r = reasoner(&lib);
    r.saturate().unwrap();
    // The instance of `受教育权利 张三` is derived but defeated by the strict
    // fact, so the rule must not fire.
    assert!(!r.knows(&atom("获得保障", "张三")));
    let conflict = r
        .conflict_for(&atom("受教育权利", "张三"))
        .expect("the conflicting instance is recorded");
    assert_eq!(
        conflict.resolution,
        std_deduce_reason::Resolution::Defeated {
            winner: std_deduce_reason::Side::Right,
            basis: std_deduce_reason::ResolutionBasis::Assumption,
        },
        "the strict fact defeats the universal instance"
    );
}
