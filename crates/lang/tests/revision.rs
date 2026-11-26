//! Parser and loader tests for `revision <标识>`: the declared group of rules
//! that are historical versions of one provision.
//!
//! Grouping is a declaration, never an inference. The loader checks what the
//! declaration implies: a group needs at least two rules, every version needs an
//! effective range, the identifier shares the declaration name space, and two
//! versions may not reuse a rule name. It never picks a version and never
//! compares their severity.

use std_deduce_kernel::meta::RevisionGroup;
use std_deduce_kernel::DeclKind;
use std_deduce_lang::ast::Item;
use std_deduce_lang::parser::parse;
use std_deduce_lang::{Library, LoadError};

fn example_rule(version: &str, effective: &str, revision: &str) -> String {
    format!(
        "rule {version} :\n  \
           params p : 人\n  \
           premise 行为 p\n  \
           conclude 应适用 p\n  \
           effective {effective}\n  \
           revision {revision}\n  \
           source text \"示例刑法\" locator \"第二十条（{version}）\"\n"
    )
}

fn program(rules: &str) -> String {
    format!(
        "sort 人\npred 行为 : 人 → Prop\npred 应适用 : 人 → Prop\nobj 甲 : 人\n\
         axiom 事 : 行为 甲\n  source text \"示例卷宗\" locator \"行为\"\n{rules}"
    )
}

fn load(src: &str) -> Result<Library, LoadError> {
    let mut lib = Library::new();
    lib.load("t", src)?;
    Ok(lib)
}

fn load_error(rules: &str) -> String {
    let error = match load(&program(rules)) {
        Ok(_) => panic!("the theory must be refused"),
        Err(error) => error,
    };
    error.render("t.std")
}

#[test]
fn a_revision_clause_parses_with_its_position() {
    let src = program(&example_rule("旧版", "1999-01-01", "第二十条"));
    let items = parse(&src).expect("the revision clause parses");
    let Some(Item::Rule { revision, .. }) =
        items.iter().find(|item| matches!(item, Item::Rule { .. }))
    else {
        panic!("expected a rule");
    };
    let revision = revision.as_ref().expect("the clause must be recorded");
    assert_eq!(revision.id, "第二十条");
    // The position points at the `revision` keyword, so load errors about the
    // group can be located.
    assert_eq!((revision.line, revision.col), (12, 3));
}

#[test]
fn the_group_is_stored_on_the_rule_declaration() {
    let src = program(&format!(
        "{}{}",
        example_rule("旧版", "1999-01-01", "第二十条"),
        example_rule("新版", "2021-01-01", "第二十条"),
    ));
    let lib = load(&src).expect("two versions form a group");
    let decl = lib.env.get("旧版").expect("the rule is declared");
    let DeclKind::Rule(rule) = &decl.kind else {
        panic!("`旧版` must be a rule");
    };
    assert_eq!(rule.revision.as_deref(), Some("第二十条"));
    // The kernel view groups both rules under the bare identifier, because a
    // case file has no namespace.
    let group = lib
        .env
        .revision_group_of(&std_deduce_kernel::name("旧版"))
        .expect("the rule declares a group");
    assert_eq!(group.declared_in, None);
    assert_eq!(group.revision.as_ref(), "第二十条");
    let groups = lib.env.revision_groups();
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].0, group);
    assert_eq!(
        groups[0].1,
        vec![
            std_deduce_kernel::name("旧版"),
            std_deduce_kernel::name("新版"),
        ]
    );
}

#[test]
fn a_rule_without_revision_has_no_group() {
    let src = program(&format!(
        "{}{}\
         rule 无关 :\n  params p : 人\n  premise 行为 p\n  conclude 应适用 p\n  \
         effective 1999-01-01\n  source text \"示例刑法\" locator \"第二十一条\"\n",
        example_rule("旧版", "1999-01-01", "第二十条"),
        example_rule("新版", "2021-01-01", "第二十条"),
    ));
    let lib = load(&src).expect("a rule outside a group is legal");
    assert_eq!(
        lib.env.revision_group_of(&std_deduce_kernel::name("无关")),
        None
    );
}

#[test]
fn a_group_identifier_is_scoped_by_the_declaring_namespace() {
    let one = "namespace a.rev\n\
               sort a.rev.人\n\
               pred a.rev.行为 : a.rev.人 → Prop\n\
               pred a.rev.应适用 : a.rev.人 → Prop\n\
               rule a.rev.旧 :\n  params p : a.rev.人\n  premise a.rev.行为 p\n  \
               conclude a.rev.应适用 p\n  effective 1999-01-01\n  revision 第二十条\n  \
               source text \"示例刑法\" locator \"第二十条\"\n\
               rule a.rev.新 :\n  params p : a.rev.人\n  premise a.rev.行为 p\n  \
               conclude a.rev.应适用 p\n  effective 2021-01-01\n  revision 第二十条\n  \
               source text \"示例刑法\" locator \"第二十条\"\n";
    let two = "namespace b.rev\n\
               sort b.rev.人\n\
               pred b.rev.行为 : b.rev.人 → Prop\n\
               pred b.rev.应适用 : b.rev.人 → Prop\n\
               rule b.rev.旧 :\n  params p : b.rev.人\n  premise b.rev.行为 p\n  \
               conclude b.rev.应适用 p\n  effective 1999-01-01\n  revision 第二十条\n  \
               source text \"示例刑法\" locator \"第二十条\"\n\
               rule b.rev.新 :\n  params p : b.rev.人\n  premise b.rev.行为 p\n  \
               conclude b.rev.应适用 p\n  effective 2021-01-01\n  revision 第二十条\n  \
               source text \"示例刑法\" locator \"第二十条\"\n";
    let mut lib = Library::new();
    lib.load("a", one).expect("the first module loads");
    lib.load("b", two).expect("the second module loads");
    let groups = lib.env.revision_groups();
    // The identifier alone is not the group: two packages may each group their
    // own `第二十条` versions without merging.
    assert_eq!(groups.len(), 2);
    assert_eq!(
        groups[0].0,
        RevisionGroup {
            declared_in: Some(std_deduce_kernel::name("a.rev")),
            revision: std_deduce_kernel::name("第二十条"),
        }
    );
    assert_eq!(groups[0].0.label(), "a.rev.第二十条");
    assert_eq!(groups[1].0.label(), "b.rev.第二十条");
}

#[test]
fn a_second_load_may_add_a_version_to_an_existing_group() {
    let src = program(&format!(
        "{}{}",
        example_rule("旧版", "1999-01-01", "第二十条"),
        example_rule("新版", "2021-01-01", "第二十条"),
    ));
    let mut lib = load(&src).expect("two versions form a group");
    // One more version of the same provision, in a second file. The group
    // already has two rules, so this single declaration completes it rather
    // than forming a group of one. The second file may reference the loaded
    // sorts and predicates, so it does not redeclare them.
    let extra = example_rule("修正版", "2023-01-01", "第二十条");
    lib.load("t2", &extra).expect("the group grows");
    assert_eq!(
        lib.env.revision_groups()[0].1,
        vec![
            std_deduce_kernel::name("旧版"),
            std_deduce_kernel::name("新版"),
            std_deduce_kernel::name("修正版"),
        ]
    );
}

#[test]
fn one_rule_is_not_a_group() {
    let error = load_error(&example_rule("旧版", "1999-01-01", "第二十条"));
    assert!(error.contains("至少有两条规则"), "{error}");
    assert!(
        error.contains("第二十条") && error.contains("单条声明"),
        "{error}"
    );
    assert!(error.contains("t.std:12:3: error:"), "{error}");
}

#[test]
fn two_versions_of_one_group_may_not_reuse_a_rule_name() {
    let rules = format!(
        "{}{}",
        example_rule("旧版", "1999-01-01", "第二十条"),
        example_rule("旧版", "2021-01-01", "第二十条"),
    );
    let error = load_error(&rules);
    assert!(
        error.contains("同一 revision 组内不能有同名规则"),
        "{error}"
    );
    assert!(error.contains("`旧版`"), "{error}");
    // The error points at the second rule's `revision` clause.
    assert!(error.contains("t.std:19:3: error:"), "{error}");
}

#[test]
fn every_version_must_declare_an_effective_range() {
    let rules = format!(
        "{}{}",
        example_rule("旧版", "1999-01-01", "第二十条"),
        "rule 新版 :\n  params p : 人\n  premise 行为 p\n  conclude 应适用 p\n  \
         revision 第二十条\n  source text \"示例刑法\" locator \"第二十条（新版）\"\n",
    );
    let error = load_error(&rules);
    assert!(error.contains("历史版本必须声明生效区间"), "{error}");
    // The error points at the version that lacks the clause, not at the first
    // version that happens to carry one.
    assert!(error.contains("`rule 新版`"), "{error}");
}

#[test]
fn the_group_identifier_may_not_be_a_declared_predicate() {
    let rules = format!(
        "{}{}",
        example_rule("旧版", "1999-01-01", "行为"),
        example_rule("新版", "2021-01-01", "行为"),
    );
    let error = load_error(&rules);
    assert!(
        error.contains("组标识不得与已声明规则名/谓词冲突"),
        "{error}"
    );
    assert!(error.contains("`行为` 已声明为 `pred`"), "{error}");
}

#[test]
fn the_group_identifier_may_not_be_a_declared_rule_name() {
    let error = load_error(&example_rule("旧版", "1999-01-01", "旧版"));
    assert!(
        error.contains("组标识不得与已声明规则名/谓词冲突"),
        "{error}"
    );
    assert!(error.contains("已声明为 `rule`"), "{error}");
}

#[test]
fn a_module_group_identifier_may_not_clash_with_its_qualified_form() {
    let src = "namespace a.rev\n\
               sort a.rev.人\n\
               pred a.rev.行为 : a.rev.人 → Prop\n\
               pred a.rev.应适用 : a.rev.人 → Prop\n\
               rule a.rev.旧 :\n  params p : a.rev.人\n  premise a.rev.行为 p\n  \
               conclude a.rev.应适用 p\n  effective 1999-01-01\n  revision a.rev.旧\n  \
               source text \"示例刑法\" locator \"第二十条\"\n\
               rule a.rev.新 :\n  params p : a.rev.人\n  premise a.rev.行为 p\n  \
               conclude a.rev.应适用 p\n  effective 2021-01-01\n  revision a.rev.旧\n  \
               source text \"示例刑法\" locator \"第二十条\"\n";
    let mut lib = Library::new();
    let error = lib.load("a", src).expect_err("the identifier names a rule");
    let rendered = error.render("a.std");
    assert!(
        rendered.contains("组标识不得与已声明规则名/谓词冲突"),
        "{rendered}"
    );
    assert!(
        rendered.contains("`a.rev.旧` 已声明为 `rule`"),
        "{rendered}"
    );
}

#[test]
fn a_lone_revision_in_a_module_is_still_a_group_of_one() {
    let src = "namespace a.rev\n\
               sort a.rev.人\n\
               pred a.rev.行为 : a.rev.人 → Prop\n\
               pred a.rev.应适用 : a.rev.人 → Prop\n\
               rule a.rev.旧 :\n  params p : a.rev.人\n  premise a.rev.行为 p\n  \
               conclude a.rev.应适用 p\n  effective 1999-01-01\n  revision 第二十条\n  \
               source text \"示例刑法\" locator \"第二十条\"\n";
    let mut lib = Library::new();
    let error = lib.load("a", src).expect_err("a group of one is refused");
    assert!(error.to_string().contains("至少有两条规则"), "{error}");
}

#[test]
fn repeated_and_misplaced_revision_clauses_are_parse_errors() {
    let duplicate = format!(
        "{}  revision 第二十一条\n",
        example_rule("旧版", "1999-01-01", "第二十条")
    );
    let error = parse(&program(&duplicate)).expect_err("a repeated clause is refused");
    assert!(error.msg.contains("revision 重复声明"), "{error}");

    // A clause crammed onto the previous line is refused instead of swallowed.
    let same_line = "rule 旧版 :\n  params p : 人\n  premise 行为 p\n  conclude 应适用 p\n  \
                     effective 1999-01-01 revision 第二十条\n  \
                     source text \"示例刑法\" locator \"第二十条\"\n";
    let error = parse(&program(same_line)).expect_err("the clause must own its line");
    assert!(error.msg.contains("`revision` 子句必须另起一行"), "{error}");

    // The value is a bare identifier, not a string literal.
    let quoted = "rule 旧版 :\n  params p : 人\n  premise 行为 p\n  conclude 应适用 p\n  \
                  effective 1999-01-01\n  revision \"第二十条\"\n  \
                  source text \"示例刑法\" locator \"第二十条\"\n";
    let error = parse(&program(quoted)).expect_err("a string is not an identifier");
    assert!(error.msg.contains("必须是裸标识符"), "{error}");

    // `revision` belongs to a rule, not to a fact and not to the top level.
    let on_fact = "sort 人\npred 行为 : 人 → Prop\naxiom 事 : 行为 甲\n  revision 甲\n  \
                   source text \"示例卷宗\" locator \"行为\"\n";
    let error = parse(on_fact).expect_err("a fact cannot carry a revision");
    assert!(
        error.msg.contains("`revision` 只能写在规则（rule）上"),
        "{error}"
    );
    let top_level = "sort 人\nrevision 甲\n";
    let error = parse(top_level).expect_err("a revision is not a declaration");
    assert!(
        error.msg.contains("`revision` 只能作为规则的子句"),
        "{error}"
    );
}
