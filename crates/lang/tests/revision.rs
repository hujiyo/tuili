//! Parser and loader tests for `revision <标识>`: the declared group of rules
//! that are historical versions of one provision.
//!
//! Grouping is a declaration, never an inference. The loader checks what the
//! declaration implies: a group needs at least two rules, every version needs an
//! effective range, the identifier shares the declaration name space, and two
//! versions may not reuse a rule name. It never picks a version and never
//! compares their severity. Group identity is a module namespace, or — for a
//! case file — the file it was loaded from.

use std_deduce_kernel::meta::{RevisionGroup, RevisionScope};
use std_deduce_kernel::DeclKind;
use std_deduce_lang::ast::Item;
use std_deduce_lang::parser::parse;
use std_deduce_lang::{Library, LoadError, LoadOptions};

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
    // A case file's group is scoped by the load identity it was read under, so
    // two case files cannot merge their versions.
    let group = rule.revision.as_ref().expect("the clause must be recorded");
    assert_eq!(
        group.scope,
        RevisionScope::File(std_deduce_kernel::name("t"))
    );
    assert_eq!(group.revision.as_ref(), "第二十条");
    assert_eq!(group.label(), "第二十条");
    assert_eq!(
        lib.env
            .revision_group_of(&std_deduce_kernel::name("旧版"))
            .as_ref(),
        Some(group)
    );
    let groups = lib.env.revision_groups();
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].0, *group);
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
    let module = |namespace: &str| {
        format!(
            "namespace {namespace}\n\
             sort {namespace}.人\n\
             pred {namespace}.行为 : {namespace}.人 → Prop\n\
             pred {namespace}.应适用 : {namespace}.人 → Prop\n\
             rule {namespace}.旧 :\n  params p : {namespace}.人\n  premise {namespace}.行为 p\n  \
             conclude {namespace}.应适用 p\n  effective 1999-01-01\n  revision 第二十条\n  \
             source text \"示例刑法\" locator \"第二十条\"\n\
             rule {namespace}.新 :\n  params p : {namespace}.人\n  premise {namespace}.行为 p\n  \
             conclude {namespace}.应适用 p\n  effective 2021-01-01\n  revision 第二十条\n  \
             source text \"示例刑法\" locator \"第二十条\"\n"
        )
    };
    let mut lib = Library::new();
    lib.load("a", &module("a.rev"))
        .expect("the first module loads");
    lib.load("b", &module("b.rev"))
        .expect("the second module loads");
    let groups = lib.env.revision_groups();
    // The identifier alone is not the group: two packages may each group their
    // own `第二十条` versions without merging.
    assert_eq!(groups.len(), 2);
    assert_eq!(
        groups[0].0,
        RevisionGroup {
            scope: RevisionScope::Namespace(std_deduce_kernel::name("a.rev")),
            revision: std_deduce_kernel::name("第二十条"),
        }
    );
    assert_eq!(groups[0].0.label(), "a.rev.第二十条");
    assert_eq!(groups[1].0.label(), "b.rev.第二十条");
}

#[test]
fn two_case_files_never_share_a_group() {
    // Each case file groups two of its own versions under the same identifier.
    // The file is the group's scope, so the two files form two groups; neither
    // completes the other's.
    let case = |suffix: &str| {
        format!(
            "sort 人{suffix}\npred 行为{suffix} : 人{suffix} → Prop\n\
             pred 应适用{suffix} : 人{suffix} → Prop\nobj 甲{suffix} : 人{suffix}\n\
             rule 旧{suffix} :\n  params p : 人{suffix}\n  premise 行为{suffix} p\n  \
             conclude 应适用{suffix} p\n  effective 1999-01-01\n  revision 第二十条\n  \
             source text \"示例刑法\" locator \"第二十条（旧）\"\n\
             rule 新{suffix} :\n  params p : 人{suffix}\n  premise 行为{suffix} p\n  \
             conclude 应适用{suffix} p\n  effective 2021-01-01\n  revision 第二十条\n  \
             source text \"示例刑法\" locator \"第二十条（新）\"\n"
        )
    };
    let mut lib = Library::new();
    lib.load("案件一.std", &case("一"))
        .expect("the first case file forms its own group");
    lib.load("案件二.std", &case("二"))
        .expect("the second case file forms its own group");
    let groups = lib.env.revision_groups();
    assert_eq!(groups.len(), 2, "{groups:?}");
    assert_eq!(groups[0].0.scope_name().as_ref(), "案件一.std");
    assert_eq!(groups[1].0.scope_name().as_ref(), "案件二.std");
    // Both print the identifier alone; their identity still differs.
    assert_eq!(groups[0].0.label(), "第二十条");
    assert_eq!(groups[1].0.label(), "第二十条");
}

#[test]
fn two_case_files_cannot_complete_each_others_single_member_group() {
    // Each file declares one version of the same provision. Because the file is
    // the group scope, they are two groups of one member each: both are refused
    // and neither is read as the other's missing version.
    let case = program(
        "rule 唯一 :\n  params p : 人\n  premise 行为 p\n  conclude 应适用 p\n  \
         effective 1999-01-01\n  revision 第二十条\n  \
         source text \"示例刑法\" locator \"第二十条\"\n",
    );
    for name in ["案件一.std", "案件二.std"] {
        let mut lib = Library::new();
        let error = lib
            .load(name, &case)
            .expect_err("a group of one is refused");
        assert!(
            error.to_string().contains(
                "组 `第二十条` 只声明了 1 个成员，历史版本至少需要 2 个；\
                 其余版本应与本次加载一起提供"
            ),
            "{error}"
        );
        // The refused load left the library unchanged, so the group is not a
        // half-built member of the environment.
        assert!(lib.env.revision_groups().is_empty());
    }
}

#[test]
fn a_pack_may_split_one_group_across_files_in_one_transaction() {
    // A law pack may keep one version per theory file. Loading one file alone
    // leaves a group of one and fails; loading both inside one transaction and
    // checking at the end succeeds.
    let base = "namespace a.rev\n\
                sort a.rev.人\n\
                pred a.rev.行为 : a.rev.人 → Prop\n\
                pred a.rev.应适用 : a.rev.人 → Prop\n";
    let rule = |rule: &str, effective: &str| {
        format!(
            "rule a.rev.{rule} :\n  params p : a.rev.人\n  premise a.rev.行为 p\n  \
             conclude a.rev.应适用 p\n  effective {effective}\n  revision 第二十条\n  \
             source text \"示例刑法\" locator \"第二十条（{rule}）\"\n"
        )
    };
    let a = format!("{base}{}", rule("旧", "1999-01-01"));
    // The second file reuses the module's sorts and predicates; it only adds
    // its own version of the provision.
    let b = format!("namespace a.rev\n{}", rule("新", "2021-01-01"));

    // One file alone: the transaction ends with a group of one and is refused.
    let mut alone = Library::new();
    let error = alone
        .load("a.std", &a)
        .expect_err("a single file of a split group is refused");
    assert!(error.to_string().contains("只声明了 1 个成员"), "{error}");

    // The same files as one transaction: the per-file load does not judge group
    // completeness, and the check after both files passes.
    let mut lib = Library::new();
    lib.load_with_options("a.std", &a, &LoadOptions::default())
        .expect("the first half of a pack transaction loads");
    lib.load_with_options("b.std", &b, &LoadOptions::default())
        .expect("the second half of a pack transaction loads");
    lib.check_revision_groups()
        .expect("the completed group has two members");
    assert_eq!(lib.env.revision_groups().len(), 1);
    assert_eq!(lib.env.revision_groups()[0].1.len(), 2);
}

#[test]
fn a_second_load_may_add_a_version_to_an_existing_group() {
    // Two files of the same module namespace, each contributing versions of one
    // provision. The second load extends the group, so the environment-wide
    // check sees all members.
    let base = "namespace a.rev\n\
                sort a.rev.人\n\
                pred a.rev.行为 : a.rev.人 → Prop\n\
                pred a.rev.应适用 : a.rev.人 → Prop\n";
    let rule = |rule: &str, effective: &str| {
        format!(
            "rule a.rev.{rule} :\n  params p : a.rev.人\n  premise a.rev.行为 p\n  \
             conclude a.rev.应适用 p\n  effective {effective}\n  revision 第二十条\n  \
             source text \"示例刑法\" locator \"第二十条（{rule}）\"\n"
        )
    };
    let mut lib = Library::new();
    lib.load(
        "a.std",
        &format!(
            "{base}{}{}",
            rule("旧", "1999-01-01"),
            rule("新", "2021-01-01")
        ),
    )
    .expect("two versions form a group");
    // A third version arrives in a second file of the same namespace.
    lib.load(
        "b.std",
        &format!("namespace a.rev\n{}", rule("修正", "2023-01-01")),
    )
    .expect("the group grows");
    let members = &lib.env.revision_groups()[0].1;
    assert_eq!(members.len(), 3);
    assert_eq!(
        members
            .iter()
            .map(|name| name.to_string())
            .collect::<Vec<_>>(),
        vec!["a.rev.旧", "a.rev.新", "a.rev.修正"]
    );
}

#[test]
fn one_rule_is_not_a_group() {
    let error = load_error(&example_rule("旧版", "1999-01-01", "第二十条"));
    assert!(
        error.contains(
            "组 `第二十条` 只声明了 1 个成员，历史版本至少需要 2 个；\
             其余版本应与本次加载一起提供"
        ),
        "{error}"
    );
    // The environment-wide check has no source position for the group; it names
    // the group instead of inventing one.
    assert!(error.starts_with("t.std: error:"), "{error}");
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
    // The error names the version that lacks the clause, not the first version
    // that happens to carry one.
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
    assert!(error.to_string().contains("只声明了 1 个成员"), "{error}");
    assert!(
        error.to_string().contains("a.rev.第二十条"),
        "the module group is qualified by its namespace: {error}"
    );
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
