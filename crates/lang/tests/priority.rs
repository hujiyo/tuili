//! Top-level `priority` declarations: a module asserts that one rule outranks
//! another and records the source of the order. Rule-internal `defeated_by` /
//! `prefer` clauses only order rules of their own package.

use std_deduce_lang::ast::Item;
use std_deduce_lang::parser::parse;
use std_deduce_lang::Library;

/// Module `a` with two well-typed rules and no priority. The error cases
/// append a `priority` line so they start from a valid module.
const MODULE_A: &str = r#"
namespace a
sort a.公民
pred a.P : a.公民 → Prop
rule a.r1 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  source text "测试" locator "一"
rule a.r2 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  source text "测试" locator "二"
"#;

/// A second package that orders `a.r1` against its own rule `b.r2`.
const PACKAGE_B: &str = r#"
namespace b
pred b.P : Prop
rule b.r2 :
  premise b.P
  conclude b.P
  source text "测试" locator "二"
priority a.r1 over b.r2 source text "上位法" locator "第一条"
"#;

const PACKAGE_B_DEFEATED_BY_A: &str = r#"
import a
namespace b
pred b.P : Prop
rule b.r2 :
  premise b.P
  conclude b.P
  defeated_by a.r1
  source text "测试" locator "二"
"#;

const PACKAGE_B_PREFER_A: &str = r#"
import a
namespace b
pred b.P : Prop
rule b.r2 :
  premise b.P
  conclude b.P
  prefer a.r1
  source text "测试" locator "二"
"#;

const MODULE_A_SAME_PACKAGE_ORDER: &str = r#"
namespace a
sort a.公民
pred a.P : a.公民 → Prop
rule a.r1 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  defeated_by a.r2
  source text "测试" locator "一"
rule a.r2 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  source text "测试" locator "二"
"#;

fn load(src: &str) -> Result<Library, String> {
    let mut lib = Library::new();
    lib.load("test.std", src)
        .map(|_| lib)
        .map_err(|e| e.to_string())
}

fn load_error(src: &str) -> String {
    load(src).expect_err("the load must fail")
}

#[test]
fn a_module_priority_loads_with_its_provenance() {
    let src = format!(
        "{MODULE_A}priority a.r1 over a.r2 source text \"上位法\" locator \"第一条\" source text \"特别法\" locator \"第二条\"\n"
    );
    let mut lib = Library::new();
    let report = lib.load("a.std", &src).expect("the priority must load");
    // The CLI prints every declaration of the load report as `+ <declaration>`.
    assert!(
        report
            .declared
            .iter()
            .any(|declared| declared == "priority a.r1 over a.r2"),
        "the load report must name the priority: {:?}",
        report.declared
    );

    let priorities = lib.env.priorities();
    assert_eq!(priorities.len(), 1, "{priorities:?}");
    let priority = &priorities[0];
    assert_eq!(priority.name.as_ref(), "priority:a:a.r1:a.r2");
    assert_eq!(priority.winner.as_ref(), "a.r1");
    assert_eq!(priority.loser.as_ref(), "a.r2");
    assert_eq!(priority.declared_in.as_ref(), "a");
    assert_eq!(priority.sources.len(), 2, "{:?}", priority.sources);
    assert_eq!(priority.sources[0].text, "上位法");
    assert_eq!(priority.sources[0].locator, "第一条");
    assert_eq!(priority.sources[1].text, "特别法");
    assert_eq!(priority.sources[1].locator, "第二条");

    let theory = lib.theory("a").expect("the namespace names the theory");
    assert!(
        theory
            .decls
            .iter()
            .any(|declared| declared == "priority:a:a.r1:a.r2"),
        "the theory must record the synthetic declaration: {:?}",
        theory.decls
    );
}

#[test]
fn parser_reads_multiple_sources_for_a_priority() {
    let items = parse(
        "priority a.r1 over a.r2 source text \"甲法\" locator \"一\" source text \"乙法\" locator \"二\"\n",
    )
    .expect("a priority with two sources parses");
    assert_eq!(items.len(), 1);
    match &items[0] {
        Item::Priority {
            winner,
            loser,
            sources,
        } => {
            assert_eq!(winner, "a.r1");
            assert_eq!(loser, "a.r2");
            assert_eq!(sources.len(), 2, "{sources:?}");
            assert_eq!(sources[0].text, "甲法");
            assert_eq!(sources[0].locator, "一");
            assert_eq!(sources[1].text, "乙法");
            assert_eq!(sources[1].locator, "二");
        }
        other => panic!("expected a priority item, got {other:?}"),
    }
}

/// The loader requires at least one usable source; the parser only collects
/// what was written, so an absent source is a load error that names the
/// declaration, exactly like a rule without provenance.
#[test]
fn parser_accepts_a_priority_without_a_source() {
    let items = parse("priority a.r1 over a.r2\n").expect("zero sources parse");
    match &items[0] {
        Item::Priority { sources, .. } => {
            assert!(sources.is_empty(), "the parser must not invent a source");
        }
        other => panic!("expected a priority item, got {other:?}"),
    }
}

#[test]
fn a_priority_source_may_start_on_the_next_line() {
    // The README spells a priority over two lines: its provenance follows the
    // declaration. `source` never starts a new item, so this is unambiguous.
    let src = format!(
        "{MODULE_A}priority a.r1 over a.r2\n  source text \"中华人民共和国立法法\" locator \"第九十二条\"\n"
    );
    let lib = load(&src).expect("a source on the following line must load");
    let priorities = lib.env.priorities();
    assert_eq!(priorities.len(), 1, "{priorities:?}");
    let sources = &priorities[0].sources;
    assert_eq!(sources.len(), 1, "{sources:?}");
    assert_eq!(sources[0].text, "中华人民共和国立法法");
    assert_eq!(sources[0].locator, "第九十二条");
}

#[test]
fn each_priority_source_may_start_on_its_own_line() {
    let src = format!(
        "{MODULE_A}priority a.r1 over a.r2\n  source text \"甲法\" locator \"一\"\n  source text \"乙法\" locator \"二\"\n"
    );
    let lib = load(&src).expect("every source may start on its own line");
    let priorities = lib.env.priorities();
    assert_eq!(priorities.len(), 1, "{priorities:?}");
    let sources = &priorities[0].sources;
    assert_eq!(sources.len(), 2, "{sources:?}");
    assert_eq!(sources[0].text, "甲法");
    assert_eq!(sources[0].locator, "一");
    assert_eq!(sources[1].text, "乙法");
    assert_eq!(sources[1].locator, "二");
}

#[test]
fn a_priority_without_a_source_leaves_the_next_declaration_alone() {
    let items = parse("priority a.r1 over a.r2\npred a.Q : Prop\n")
        .expect("the parser must not read the next declaration as a source");
    assert_eq!(items.len(), 2, "{items:?}");
    match &items[0] {
        Item::Priority { sources, .. } => assert!(sources.is_empty(), "{sources:?}"),
        other => panic!("expected a priority item, got {other:?}"),
    }
}

#[test]
fn parser_requires_the_over_keyword() {
    let err = parse("priority a.r1 a.r2\n").expect_err("`over` is required");
    assert_eq!(err.line, 1, "{err}");
    assert_eq!(
        err.col, 15,
        "the error points at the token that replaced `over`"
    );
    assert!(err.msg.contains("缺少 `over`"), "{err}");
    assert!(
        err.msg.contains("priority <胜者规则> over <败者规则>"),
        "the message must show the expected shape: {err}"
    );
}

#[test]
fn a_priority_needs_a_usable_source() {
    for src in [
        format!("{MODULE_A}priority a.r1 over a.r2\n"),
        format!("{MODULE_A}priority a.r1 over a.r2 source text \" \" locator \" \"\n"),
    ] {
        let err = load_error(&src);
        assert!(err.contains("优先关系必须有出处"), "got: {err}");
        assert!(err.contains("priority a.r1 over a.r2"), "got: {err}");
        assert!(err.contains("没有出处的裁决不能被当作已证明"), "got: {err}");
    }
}

#[test]
fn a_priority_cannot_point_at_itself() {
    let err = load_error(&format!(
        "{MODULE_A}priority a.r1 over a.r1 source text \"测试\" locator \"一\"\n"
    ));
    assert!(err.contains("priority a.r1 over a.r1"), "got: {err}");
    assert!(err.contains("不能指向自己"), "got: {err}");
}

#[test]
fn a_rule_clause_cannot_point_at_itself() {
    for clause in ["defeated_by", "prefer"] {
        let src = format!(
            r#"
namespace a
sort a.公民
pred a.P : a.公民 → Prop
rule a.r1 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  {clause} a.r1
  source text "测试" locator "一"
"#
        );
        let err = load_error(&src);
        assert!(err.contains("`rule a.r1`"), "for {clause:?}, got: {err}");
        assert!(
            err.contains(&format!("`{clause}`")),
            "for {clause:?}, got: {err}"
        );
        assert!(err.contains("指向自己"), "for {clause:?}, got: {err}");
        assert!(
            err.contains("规则不能优先于自身"),
            "for {clause:?}, got: {err}"
        );
    }
}

#[test]
fn a_rule_clause_may_point_at_another_rule() {
    for clause in ["defeated_by", "prefer"] {
        let src = format!(
            r#"
namespace a
sort a.公民
pred a.P : a.公民 → Prop
rule a.r1 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  {clause} a.r2
  source text "测试" locator "一"
rule a.r2 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  source text "测试" locator "二"
"#
        );
        load(&src).unwrap_or_else(|e| panic!("`{clause} a.r2` must stay legal: {e}"));
    }
}

#[test]
fn a_priority_target_must_be_an_existing_rule() {
    for (priority, needle) in [
        ("priority a.ghost over a.r2", "未知规则 `a.ghost`"),
        ("priority a.r1 over a.ghost", "未知规则 `a.ghost`"),
        ("priority a.P over a.r1", "`a.P` 不是规则"),
        ("priority a.r1 over a.P", "`a.P` 不是规则"),
    ] {
        let err = load_error(&format!(
            "{MODULE_A}{priority} source text \"测试\" locator \"一\"\n"
        ));
        assert!(err.contains(needle), "for {priority:?}, got: {err}");
        assert!(
            err.contains(priority),
            "the error must name the declaration {priority:?}: {err}"
        );
    }
}

#[test]
fn a_priority_may_name_a_rule_declared_later_in_the_same_file() {
    let src = r#"
namespace a
sort a.公民
pred a.P : a.公民 → Prop
priority a.r1 over a.r2 source text "上位法" locator "第一条"
rule a.r1 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  source text "测试" locator "一"
rule a.r2 :
  params x : a.公民
  premise a.P x
  conclude a.P x
  source text "测试" locator "二"
"#;
    let lib = load(src).expect("a priority may name a rule declared later in the same file");
    assert_eq!(lib.env.priorities().len(), 1);
}

#[test]
fn a_duplicate_priority_is_refused_and_the_reverse_order_is_kept() {
    let duplicate = format!(
        "{MODULE_A}priority a.r1 over a.r2 source text \"甲\" locator \"一\"\npriority a.r1 over a.r2 source text \"乙\" locator \"二\"\n"
    );
    let err = load_error(&duplicate);
    assert!(err.contains("priority a.r1 over a.r2"), "got: {err}");
    assert!(err.contains("这一条已经声明过了"), "got: {err}");

    // The opposite direction is a distinct claim, not a duplicate.
    let reverse = format!(
        "{MODULE_A}priority a.r1 over a.r2 source text \"甲\" locator \"一\"\npriority a.r2 over a.r1 source text \"乙\" locator \"二\"\n"
    );
    let lib = load(&reverse).expect("the reverse order is a competing claim, not a duplicate");
    let priorities = lib.env.priorities();
    assert_eq!(priorities.len(), 2, "{priorities:?}");
    assert_eq!(
        (priorities[0].winner.as_ref(), priorities[0].loser.as_ref()),
        ("a.r1", "a.r2")
    );
    assert_eq!(
        (priorities[1].winner.as_ref(), priorities[1].loser.as_ref()),
        ("a.r2", "a.r1")
    );
}

#[test]
fn a_cross_package_priority_requires_an_explicit_import() {
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A).expect("a loads");

    let err = lib
        .load("b.std", PACKAGE_B)
        .expect_err("a target in an unimported package must be refused")
        .to_string();
    assert!(err.contains("priority a.r1 over b.r2"), "got: {err}");
    assert!(err.contains("没有 `import a`"), "got: {err}");
    assert!(err.contains("必须显式 import 目标包"), "got: {err}");
    assert!(
        lib.theory("b").is_none(),
        "the failed load must not record the theory"
    );
    assert!(
        lib.env.get("b.r2").is_none(),
        "the failed load leaked a declaration"
    );

    let with_import = format!("import a\n{PACKAGE_B}");
    lib.load("b.std", &with_import)
        .expect("an imported package may be ordered");
    let priorities = lib.env.priorities();
    assert_eq!(priorities.len(), 1, "{priorities:?}");
    assert_eq!(priorities[0].winner.as_ref(), "a.r1");
    assert_eq!(priorities[0].loser.as_ref(), "b.r2");
    assert_eq!(
        priorities[0].declared_in.as_ref(),
        "b",
        "the declaring package is part of the claim"
    );
}

#[test]
fn a_case_file_cannot_declare_a_priority() {
    let src = r#"
sort 申请
pred P : 申请 → Prop
rule r1 :
  params x : 申请
  premise P x
  conclude P x
  source text "测试" locator "一"
rule r2 :
  params x : 申请
  premise P x
  conclude P x
  source text "测试" locator "二"
priority r1 over r2 source text "测试" locator "三"
"#;
    let err = load_error(src);
    assert!(
        err.contains("`priority` 只能写在带 namespace 的模块里"),
        "got: {err}"
    );
    assert!(err.contains("案件文件不能声明顶层优先级"), "got: {err}");
}

#[test]
fn a_rule_clause_cannot_order_a_rule_of_another_package() {
    for (package, direction) in [
        (PACKAGE_B_DEFEATED_BY_A, "priority a.r1 over b.r2"),
        (PACKAGE_B_PREFER_A, "priority b.r2 over a.r1"),
    ] {
        let mut lib = Library::new();
        lib.load("a.std", MODULE_A).expect("a loads");
        let err = lib
            .load("b.std", package)
            .expect_err("a cross-package clause must be refused")
            .to_string();
        assert!(err.contains("规则 `b.r2`"), "got: {err}");
        assert!(err.contains("另一个包 `a` 的规则 `a.r1`"), "got: {err}");
        assert!(err.contains("跨包优先关系必须用顶层"), "got: {err}");
        assert!(err.contains(direction), "got: {err}");
        assert!(err.contains("规则内子句只用于同一包内"), "got: {err}");
    }

    // Regression: within one package the rule-internal spelling is still the
    // way to order rules.
    let lib = load(MODULE_A_SAME_PACKAGE_ORDER).expect("a same-package order is legal");
    assert!(lib.env.get("a.r1").is_some());

    // A case rule has no namespace, so naming a package rule is cross-package
    // as well: `None` and `Some` never count as the same package.
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A).expect("a loads");
    let err = lib
        .load(
            "case.std",
            "pred Q : a.公民 → Prop\nrule 案件规则 :\n  params x : a.公民\n  premise Q x\n  conclude Q x\n  defeated_by a.r1\n  source text \"案件\" locator \"一\"\n",
        )
        .expect_err("a case rule must not order a package rule")
        .to_string();
    assert!(
        err.contains("规则 `案件规则` 的 `defeated_by` 指向了另一个包 `a` 的规则 `a.r1`"),
        "got: {err}"
    );
    assert!(err.contains("跨包优先关系必须用顶层"), "got: {err}");
}

#[test]
fn a_module_priority_requires_qualified_names() {
    for (src, name) in [
        (
            "namespace a\npriority r1 over a.r2 source text \"t\" locator \"l\"\n",
            "`r1`",
        ),
        (
            "namespace a\npriority a.r1 over r2 source text \"t\" locator \"l\"\n",
            "`r2`",
        ),
    ] {
        let err = load_error(src);
        assert!(err.contains("未限定"), "for {src:?}, got: {err}");
        assert!(err.contains(name), "for {src:?}, got: {err}");
        assert!(err.contains("priority"), "for {src:?}, got: {err}");
    }
}
