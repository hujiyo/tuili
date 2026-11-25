//! Parser and loader tests for rule scope and fact occurrence metadata.
//!
//! M2-6/M2-7 record the effective range, jurisdiction/territory and occurrence
//! date/place. The loader combines a rule's written clauses with the containing
//! pack's manifest field by field; it must not filter or infer applicability.

use std_deduce_kernel::meta::{Scope, ScopeOrigin};
use std_deduce_lang::ast::{Item, ScopeSpec};
use std_deduce_lang::parser::parse;
use std_deduce_lang::{Library, LoadOptions};

const PACK_SCOPE: Scope = Scope {
    effective_from: None,
    effective_to: None,
    jurisdiction: None,
    territory: None,
    origin: ScopeOrigin::PackDefault,
};

fn pack_scope() -> Scope {
    Scope {
        effective_from: Some("1999-10-01".to_owned()),
        effective_to: Some("2021-01-01".to_owned()),
        jurisdiction: Some("CN".to_owned()),
        territory: Some("CN".to_owned()),
        origin: ScopeOrigin::PackDefault,
    }
}

fn load_with(src: &str, options: &LoadOptions) -> Library {
    let mut lib = Library::new();
    lib.load_with_options("t", src, options)
        .unwrap_or_else(|error| panic!("load failed: {error}"));
    lib
}

/// One rule with every scope clause parses into the AST exactly as written;
/// `repealed` is stored as the exclusive end.
#[test]
fn a_rule_parses_all_four_scope_clauses() {
    let src = r#"
sort 人
pred 犯规 : 人 → Prop
pred 处罚 : 人 → Prop
rule 规则 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  effective 1999-10-01
  repealed 2021-01-01
  jurisdiction CN
  territory CN-HN
  source text "测试法" locator "第一条"
"#;
    let items = parse(src).expect("the scope clauses parse");
    let Some(Item::Rule { scope, .. }) =
        items.iter().find(|item| matches!(item, Item::Rule { .. }))
    else {
        panic!("expected a rule");
    };
    assert_eq!(
        scope,
        &ScopeSpec {
            effective_from: Some("1999-10-01".to_owned()),
            effective_to: Some("2021-01-01".to_owned()),
            jurisdiction: Some("CN".to_owned()),
            territory: Some("CN-HN".to_owned()),
        }
    );
}

/// A fact parses `occurred_at` and `occurred_in` in any order with `source` and
/// `identity`; the values stay raw until the loader validates them.
#[test]
fn a_fact_parses_occurrence_clauses() {
    let src = r#"
sort 人
pred 违法 : 人 → Prop
axiom 事实 : 违法 甲
  source text "案件材料" locator "第一页"
  occurred_in CN-HN
  identity verified
  occurred_at 2020-05-06
"#;
    let items = parse(src).expect("the occurrence clauses parse");
    let Some(Item::Axiom {
        occurred_at,
        occurred_in,
        identity,
        ..
    }) = items.iter().find(|item| matches!(item, Item::Axiom { .. }))
    else {
        panic!("expected an axiom");
    };
    assert_eq!(occurred_at.as_deref(), Some("2020-05-06"));
    assert_eq!(occurred_in.as_deref(), Some("CN-HN"));
    assert_eq!(identity, &Some(std_deduce_kernel::FactIdentity::Verified));
}

/// A scope clause may follow a `source` clause without being swallowed as
/// another source field: source fields are quoted, scope clause values are bare.
#[test]
fn a_scope_clause_after_source_is_not_a_source_field() {
    let src = r#"
sort 人
pred 犯规 : 人 → Prop
pred 处罚 : 人 → Prop
rule 规则 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  source text "测试法" locator "第一条"
  jurisdiction JP
  territory JP-13
"#;
    let items = parse(src).expect("the scope clause after source parses");
    let Some(Item::Rule { scope, sources, .. }) =
        items.iter().find(|item| matches!(item, Item::Rule { .. }))
    else {
        panic!("expected a rule");
    };
    assert_eq!(sources.len(), 1);
    assert_eq!(sources[0].locator, "第一条");
    assert!(sources[0].jurisdiction.is_empty());
    assert_eq!(scope.jurisdiction.as_deref(), Some("JP"));
    assert_eq!(scope.territory.as_deref(), Some("JP-13"));
}

/// A quoted value on a new line after a source is still a source field, so the
/// source syntax keeps working unchanged.
#[test]
fn a_quoted_source_field_after_a_newline_is_still_a_source_field() {
    let src = r#"
sort 人
pred 犯规 : 人 → Prop
rule 规则 :
  params x : 人
  premise 犯规 x
  conclude 犯规 x
  source text "测试法"
    jurisdiction "CN"
    locator "第一条"
"#;
    let items = parse(src).expect("the quoted source fields parse");
    let Some(Item::Rule { scope, sources, .. }) =
        items.iter().find(|item| matches!(item, Item::Rule { .. }))
    else {
        panic!("expected a rule");
    };
    assert_eq!(sources.len(), 1);
    assert_eq!(sources[0].jurisdiction, "CN");
    assert_eq!(sources[0].locator, "第一条");
    assert_eq!(scope, &ScopeSpec::default());
}

#[test]
fn duplicate_scope_clauses_are_parse_errors() {
    for clause in [
        "effective 1999-10-01\n  effective 2000-01-01",
        "repealed 2021-01-01\n  repealed 2022-01-01",
        "jurisdiction CN\n  jurisdiction JP",
        "territory CN\n  territory JP",
    ] {
        let src = format!(
            "sort 人\npred 犯规 : 人 → Prop\npred 处罚 : 人 → Prop\n\
             rule 规则 :\n  params x : 人\n  premise 犯规 x\n  conclude 处罚 x\n  {clause}\n\
             \x20 source text \"测试法\" locator \"第一条\"\n"
        );
        let error = parse(&src).expect_err("a duplicate scope clause is a parse error");
        assert!(error.msg.contains("重复"), "{clause}: {error}");
    }
}

#[test]
fn scope_clauses_on_a_fact_are_refused() {
    for clause in [
        "effective 1999-10-01",
        "repealed 2021-01-01",
        "jurisdiction CN",
        "territory CN",
    ] {
        let src = format!(
            "sort 人\npred 违法 : 人 → Prop\naxiom 事实 : 违法 甲\n  {clause}\n\
             \x20 source text \"案件材料\" locator \"第一页\"\n"
        );
        let error = parse(&src).expect_err("a scope clause on a fact is a parse error");
        assert!(
            error.msg.contains("规则") && error.msg.contains(clause.split(' ').next().unwrap()),
            "{clause}: {error}"
        );
    }
}

#[test]
fn occurrence_clauses_on_a_rule_are_refused() {
    for clause in ["occurred_at 2020-05-06", "occurred_in CN-HN"] {
        let src = format!(
            "sort 人\npred 犯规 : 人 → Prop\npred 处罚 : 人 → Prop\n\
             rule 规则 :\n  params x : 人\n  premise 犯规 x\n  conclude 处罚 x\n  {clause}\n\
             \x20 source text \"测试法\" locator \"第一条\"\n"
        );
        let error = parse(&src).expect_err("an occurrence clause on a rule is a parse error");
        assert!(
            error.msg.contains("事实") && error.msg.contains(clause.split(' ').next().unwrap()),
            "{clause}: {error}"
        );
    }
}

/// A pack rule inherits the manifest scope field by field. A rule that writes
/// any field is `Rule`-origin; one that writes none is `PackDefault`-origin.
#[test]
fn pack_rules_inherit_missing_fields_and_record_the_origin() {
    let src = r#"
namespace pkg.a
sort pkg.a.人
pred pkg.a.犯规 : pkg.a.人 → Prop
pred pkg.a.处罚 : pkg.a.人 → Prop
rule pkg.a.继承 :
  params x : pkg.a.人
  premise pkg.a.犯规 x
  conclude pkg.a.处罚 x
  source text "测试法" locator "第一条"
rule pkg.a.部分显式 :
  params x : pkg.a.人
  premise pkg.a.犯规 x
  conclude pkg.a.处罚 x
  territory CN-HN
  source text "测试法" locator "第二条"
rule pkg.a.全显式 :
  params x : pkg.a.人
  premise pkg.a.犯规 x
  conclude pkg.a.处罚 x
  effective 2001-01-01
  repealed 2020-01-01
  jurisdiction JP
  territory JP-13
  source text "测试法" locator "第三条"
"#;
    let options = LoadOptions {
        pack_scope: Some(pack_scope()),
        case_local: false,
    };
    let lib = load_with(src, &options);

    let inherited = &lib.env.get("pkg.a.继承").expect("the rule loaded").scope;
    assert_eq!(inherited.effective_from.as_deref(), Some("1999-10-01"));
    assert_eq!(inherited.effective_to.as_deref(), Some("2021-01-01"));
    assert_eq!(inherited.jurisdiction.as_deref(), Some("CN"));
    assert_eq!(inherited.territory.as_deref(), Some("CN"));
    assert_eq!(inherited.origin, ScopeOrigin::PackDefault);

    let partial = &lib
        .env
        .get("pkg.a.部分显式")
        .expect("the rule loaded")
        .scope;
    assert_eq!(partial.effective_from.as_deref(), Some("1999-10-01"));
    assert_eq!(partial.effective_to.as_deref(), Some("2021-01-01"));
    assert_eq!(partial.jurisdiction.as_deref(), Some("CN"));
    assert_eq!(partial.territory.as_deref(), Some("CN-HN"));
    assert_eq!(partial.origin, ScopeOrigin::Rule);

    let explicit = &lib.env.get("pkg.a.全显式").expect("the rule loaded").scope;
    assert_eq!(explicit.effective_from.as_deref(), Some("2001-01-01"));
    assert_eq!(explicit.effective_to.as_deref(), Some("2020-01-01"));
    assert_eq!(explicit.jurisdiction.as_deref(), Some("JP"));
    assert_eq!(explicit.territory.as_deref(), Some("JP-13"));
    assert_eq!(explicit.origin, ScopeOrigin::Rule);
}

/// A plain module outside a pack inherits nothing: no scope means an empty
/// `Unspecified` record, not a guessed default.
#[test]
fn a_file_outside_a_pack_has_no_inherited_scope() {
    let src = r#"
sort 人
pred 犯规 : 人 → Prop
pred 处罚 : 人 → Prop
rule 规则 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  source text "测试法" locator "第一条"
"#;
    let lib = load_with(src, &LoadOptions::default());
    let scope = &lib.env.get("规则").expect("the rule loaded").scope;
    assert!(scope.is_unscoped());
    assert_eq!(scope.origin, ScopeOrigin::Unspecified);
}

/// Case-local rules never inherit a pack manifest, and they are marked
/// `CaseLocal` whether or not they write a field themselves.
#[test]
fn case_local_rules_are_case_local_and_do_not_inherit() {
    let src = r#"
sort 人
pred 犯规 : 人 → Prop
pred 处罚 : 人 → Prop
rule 本地 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  jurisdiction CN-HN
  source text "案件材料" locator "第一条"
rule 无作用域 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  source text "案件材料" locator "第二条"
"#;
    let options = LoadOptions {
        pack_scope: Some(pack_scope()),
        case_local: true,
    };
    let lib = load_with(src, &options);

    let local = &lib.env.get("本地").expect("the rule loaded").scope;
    assert_eq!(local.jurisdiction.as_deref(), Some("CN-HN"));
    assert_eq!(local.effective_from, None);
    assert_eq!(local.territory, None);
    assert_eq!(local.origin, ScopeOrigin::CaseLocal);

    let unscoped = &lib.env.get("无作用域").expect("the rule loaded").scope;
    assert!(unscoped.is_unscoped());
    assert_eq!(unscoped.origin, ScopeOrigin::CaseLocal);
}

/// A fact's occurrence defaults to `None`; nothing copies a query date (there
/// is no query date here) and an absent endpoint stays absent.
#[test]
fn fact_occurrence_defaults_to_none_and_is_never_inherited() {
    let src = r#"
sort 人
pred 违法 : 人 → Prop
pred 记录 : 人 → Prop
obj 甲 : 人
axiom 无发生记录 : 违法 甲
  source text "案件材料" locator "第一页"
axiom 有发生记录 : 记录 甲
  occurred_at 2020-05-06
  occurred_in CN-HN
  source text "案件材料" locator "第二页"
"#;
    let options = LoadOptions {
        pack_scope: Some(pack_scope()),
        case_local: false,
    };
    let lib = load_with(src, &options);
    let without = lib.env.get("无发生记录").expect("the fact loaded");
    assert_eq!(without.occurred_at, None);
    assert_eq!(without.occurred_in, None);
    let with = lib.env.get("有发生记录").expect("the fact loaded");
    assert_eq!(with.occurred_at.as_deref(), Some("2020-05-06"));
    assert_eq!(with.occurred_in.as_deref(), Some("CN-HN"));
}

/// Occurrence metadata is a fact's, not a named constant's: `axiom 假 : Prop`
/// must not carry it.
#[test]
fn occurrence_metadata_on_a_non_fact_constant_is_refused() {
    let src = r#"
sort 人
pred 违法 : 人 → Prop
axiom 命题 : Prop
  occurred_at 2020-05-06
  source text "案件材料" locator "第一页"
"#;
    let error = Library::new()
        .load("t", src)
        .expect_err("a non-fact axiom cannot record an occurrence");
    assert!(
        error.to_string().contains("occurred_at") && error.to_string().contains("事实"),
        "{error}"
    );
}

/// The loader validates scope values with the shared date/code rules and the
/// `repealed` relationship; these are load errors, not ignored metadata.
#[test]
fn invalid_scope_values_are_load_errors() {
    let cases = [
        ("repealed 2021-01-01", "repealed", "effective"),
        (
            "effective 2021-01-01\n  repealed 2020-01-01",
            "repealed",
            "晚于",
        ),
        ("effective 2021-02-30", "effective", "日期"),
        ("jurisdiction CN_HN", "jurisdiction", "非法字符"),
        ("territory CN_HN", "territory", "非法字符"),
    ];
    for (clause, needle_a, needle_b) in cases {
        let src = format!(
            "sort 人\npred 犯规 : 人 → Prop\npred 处罚 : 人 → Prop\n\
             rule 规则 :\n  params x : 人\n  premise 犯规 x\n  conclude 处罚 x\n  {clause}\n\
             \x20 source text \"测试法\" locator \"第一条\"\n"
        );
        let error = Library::new()
            .load("t", &src)
            .expect_err("an invalid scope value is a load error");
        let message = error.to_string();
        assert!(
            message.contains(needle_a) && message.contains(needle_b),
            "{clause}: {message}"
        );
    }
}

#[test]
fn invalid_occurrence_values_are_load_errors() {
    for (clause, needle) in [
        ("occurred_at 2020-02-30", "日期"),
        ("occurred_in CN_HN", "非法字符"),
    ] {
        let src = format!(
            "sort 人\npred 违法 : 人 → Prop\nobj 甲 : 人\naxiom 事实 : 违法 甲\n  {clause}\n\
             \x20 source text \"案件材料\" locator \"第一页\"\n"
        );
        let error = Library::new()
            .load("t", &src)
            .expect_err("an invalid occurrence value is a load error");
        assert!(error.to_string().contains(needle), "{clause}: {error}");
    }
}

/// The scope value validation also applies to a caller-supplied pack scope, so
/// a hand-built `LoadOptions` cannot inject an impossible date.
#[test]
fn an_invalid_pack_scope_is_refused() {
    let src = r#"
sort 人
pred 犯规 : 人 → Prop
pred 处罚 : 人 → Prop
rule 规则 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  source text "测试法" locator "第一条"
"#;
    let mut scope = pack_scope();
    scope.effective_from = Some("1999-13-01".to_owned());
    let options = LoadOptions {
        pack_scope: Some(scope),
        case_local: false,
    };
    let mut lib = Library::new();
    let error = lib
        .load_with_options("t", src, &options)
        .expect_err("an invalid inherited date must be refused");
    assert!(error.to_string().contains("effective_from"), "{error}");
    assert!(
        !lib.env.contains("规则"),
        "the failed load must insert nothing"
    );
}

/// The sentinel keeps `PACK_SCOPE` referenced without a second construction
/// path; it also documents that `origin` is ignored when the loader inherits.
#[test]
fn the_pack_scope_origin_is_ignored() {
    let src = r#"
sort 人
pred 犯规 : 人 → Prop
pred 处罚 : 人 → Prop
rule 规则 :
  params x : 人
  premise 犯规 x
  conclude 处罚 x
  source text "测试法" locator "第一条"
"#;
    let options = LoadOptions {
        pack_scope: Some(PACK_SCOPE),
        case_local: false,
    };
    let lib = load_with(src, &options);
    let scope = &lib.env.get("规则").expect("the rule loaded").scope;
    assert_eq!(scope.origin, ScopeOrigin::PackDefault);
    assert_eq!(scope.jurisdiction, None);
}
