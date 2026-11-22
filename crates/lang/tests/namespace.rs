//! Explicit namespaces: a module file declares one namespace, its declaration
//! names and references carry that prefix, and two modules may share suffixes.

use std::collections::BTreeMap;

use std_deduce_kernel::pretty::print_expr;
use std_deduce_lang::ast::Item;
use std_deduce_lang::lexer::{lex, Tok};
use std_deduce_lang::parser::parse;
use std_deduce_lang::Library;

const MODULE_A: &str = r#"
namespace a
sort a.公民
sort a.住宅
pred a.非法搜查 : a.公民 → a.住宅 → Prop
pred a.不受侵犯 : a.公民 → a.住宅 → Prop
rule a.非法搜查即侵犯 :
  params p : a.公民, h : a.住宅
  premise a.非法搜查 p h
  conclude a.不受侵犯 p h
  source text "测试" locator "一"
"#;

const MODULE_B: &str = r#"
namespace b
sort b.公民
sort b.住宅
pred b.非法搜查 : b.公民 → b.住宅 → Prop
pred b.不受侵犯 : b.公民 → b.住宅 → Prop
rule b.非法搜查即侵犯 :
  params p : b.公民, h : b.住宅
  premise b.非法搜查 p h
  conclude b.不受侵犯 p h
  source text "测试" locator "一"
"#;

fn load(src: &str) -> Result<Library, String> {
    let mut lib = Library::new();
    lib.load("test", src)
        .map(|_| lib)
        .map_err(|e| e.to_string())
}

fn snapshot(lib: &Library) -> BTreeMap<String, String> {
    lib.env
        .iter()
        .map(|decl| (decl.name.to_string(), print_expr(&decl.ty)))
        .collect()
}

#[test]
fn lexer_treats_qualified_names_as_single_tokens() {
    let tokens = lex("a.pred cn.constitution.公民 foo-bar a->b").unwrap();
    let idents: Vec<&str> = tokens
        .iter()
        .filter_map(|token| match &token.tok {
            Tok::Ident(s) => Some(s.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(
        idents,
        vec!["a.pred", "cn.constitution.公民", "foo-bar", "a", "b"]
    );
    assert_eq!(
        tokens
            .iter()
            .filter(|token| matches!(token.tok, Tok::Arrow))
            .count(),
        1,
        "`->` must stay an arrow even next to identifier characters"
    );

    // `--` still starts a comment rather than joining two identifiers.
    let tokens = lex("a-- 注释\nb").unwrap();
    let idents: Vec<&str> = tokens
        .iter()
        .filter_map(|token| match &token.tok {
            Tok::Ident(s) => Some(s.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(idents, vec!["a", "b"]);
}

#[test]
fn parser_reads_a_leading_namespace_and_qualified_declarations() {
    let items = parse(
        "-- 模块注释\nnamespace cn.constitution\n\
         sort cn.constitution.公民\n\
         pred cn.constitution.非法搜查 : cn.constitution.公民 → cn.constitution.住宅 → Prop\n",
    )
    .expect("a namespaced module parses");
    assert_eq!(
        items.first(),
        Some(&Item::Namespace("cn.constitution".into()))
    );
    match &items[1] {
        Item::Sort { name, .. } => assert_eq!(name, "cn.constitution.公民"),
        other => panic!("expected a sort, got {other:?}"),
    }
    match &items[2] {
        Item::Pred { name, .. } => assert_eq!(name, "cn.constitution.非法搜查"),
        other => panic!("expected a predicate, got {other:?}"),
    }
}

#[test]
fn parser_rejects_a_namespace_that_is_not_first_or_repeated() {
    let err = parse("sort x\nnamespace a")
        .expect_err("namespace after another item must be refused")
        .to_string();
    assert!(err.contains("第一条"), "got: {err}");

    let err = parse("namespace a\nnamespace b")
        .expect_err("a second namespace must be refused")
        .to_string();
    assert!(err.contains("只能出现一次"), "got: {err}");
}

#[test]
fn parser_rejects_malformed_namespaces() {
    for (src, needle) in [
        ("namespace A.b", "小写"),
        ("namespace a..b", "空段"),
        ("namespace a.", "空段"),
        ("namespace a-", "不能以 `-`"),
        ("namespace a b", "换行"),
        ("namespace cn.constitution.公民", "非法字符"),
        ("namespace a_b", "非法字符"),
    ] {
        let err = parse(src)
            .expect_err("a malformed namespace must not parse")
            .to_string();
        assert!(err.contains(needle), "for {src:?}, got: {err}");
    }

    for src in ["namespace", "namespace .a", "namespace -a", "namespace "] {
        assert!(
            parse(src).is_err(),
            "malformed namespace {src:?} must not parse"
        );
    }

    // Digits and internal dashes are part of the allowed format.
    assert!(parse("namespace cn.constitution-2018\nsort cn.constitution-2018.公民\n").is_ok());
}

#[test]
fn module_loads_declarations_under_its_namespace() {
    let lib = load(MODULE_A).expect("the module loads");
    let theory = lib.theory("a").expect("the namespace names the theory");
    assert_eq!(theory.name, "a");
    assert_eq!(theory.namespace.as_deref(), Some("a"));
    assert!(
        lib.theory("test").is_none(),
        "a namespaced theory must not be named after the load path"
    );

    for name in [
        "a.公民",
        "a.住宅",
        "a.非法搜查",
        "a.不受侵犯",
        "a.非法搜查即侵犯",
    ] {
        assert!(lib.env.get(name).is_some(), "missing `{name}`");
    }
    for name in ["公民", "住宅", "非法搜查", "不受侵犯", "非法搜查即侵犯"] {
        assert!(
            lib.env.get(name).is_none(),
            "unqualified `{name}` leaked into the ledger"
        );
    }
    assert!(lib
        .env
        .rules()
        .iter()
        .any(|decl| decl.name.as_ref() == "a.非法搜查即侵犯"));
}

#[test]
fn every_declaration_kind_loads_when_qualified() {
    let src = r#"
namespace a
sort a.公民
sort a.住宅
pred a.非法搜查 : a.公民 → a.住宅 → Prop
pred a.违法 : a.公民 → Prop
pred a.合法 : a.公民 → Prop
pred a.P : Prop
pred a.Q : Prop
obj a.张三 : a.公民
obj a.甲宅 : a.住宅
axiom a.事实 : a.非法搜查 a.张三 a.甲宅
  source text "测试" locator "一"
def a.侵权 : a.公民 → Prop := λ (x : a.公民) := a.违法 x
contrary a.违法 a.合法
unique a.违法 1
interpret a.解释 : a.P → a.Q
"#;
    let lib = load(src).expect("every qualified declaration kind must load");
    for name in [
        "a.公民",
        "a.住宅",
        "a.非法搜查",
        "a.违法",
        "a.合法",
        "a.P",
        "a.Q",
        "a.张三",
        "a.甲宅",
        "a.事实",
        "a.侵权",
        "a.解释",
    ] {
        assert!(lib.env.get(name).is_some(), "missing `{name}`");
    }
    assert_eq!(lib.env.contrary_pairs().len(), 1);
    assert_eq!(lib.env.unique_positions().len(), 1);
    assert_eq!(lib.env.interpretations().len(), 1);
}

#[test]
fn two_modules_with_the_same_suffixes_coexist_and_load_order_does_not_matter() {
    let mut ab = Library::new();
    ab.load("a.std", MODULE_A).expect("a loads");
    ab.load("b.std", MODULE_B).expect("b loads");

    let mut ba = Library::new();
    ba.load("b.std", MODULE_B).expect("b loads");
    ba.load("a.std", MODULE_A).expect("a loads");

    assert_eq!(
        snapshot(&ab),
        snapshot(&ba),
        "swapping module load order must not change the flat ledger"
    );
    for name in [
        "a.非法搜查",
        "b.非法搜查",
        "a.非法搜查即侵犯",
        "b.非法搜查即侵犯",
    ] {
        assert!(ab.env.get(name).is_some(), "missing `{name}`");
    }
}

#[test]
fn module_declaration_names_must_carry_the_namespace_prefix() {
    for (src, declaration) in [
        (
            "namespace a\nsort 公民\n",
            "`sort 公民`",
        ),
        (
            "namespace a\nobj 张三 : a.公民\n",
            "`obj 张三`",
        ),
        (
            "namespace a\npred 非法搜查 : a.公民 → Prop\n",
            "`pred 非法搜查`",
        ),
        (
            "namespace a\naxiom 事实 : a.命题\n",
            "`axiom 事实`",
        ),
        (
            "namespace a\ndef 侵权 : a.公民 → Prop := λ (x : a.公民) := x\n",
            "`def 侵权`",
        ),
        (
            "namespace a\nrule 规则 :\n  premise a.P\n  conclude a.Q\n  source text \"t\" locator \"l\"\n",
            "`rule 规则`",
        ),
        (
            "namespace a\ninterpret 解释 : a.P → a.Q\n",
            "`interpret 解释`",
        ),
        (
            "namespace a\nsort b.公民\n",
            "`sort b.公民`",
        ),
    ] {
        let err = load(src).expect_err("an unqualified declaration name must be refused");
        assert!(
            err.contains(declaration),
            "error should name the declaration {declaration}: {err}"
        );
        assert!(
            err.contains("`a.` 开头"),
            "error should state the required prefix: {err}"
        );
    }
}

#[test]
fn module_references_must_be_fully_qualified() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "namespace a\nsort a.公民\npred a.P : 公民 → Prop\n",
            "pred a.P",
            "公民",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\n\
             rule a.r :\n  params p : 公民\n  premise a.P p\n  conclude a.P p\n\
             \x20 source text \"t\" locator \"l\"\n",
            "a.r",
            "公民",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\n\
             rule a.r :\n  params p : a.公民\n  premise P p\n  conclude a.P p\n\
             \x20 source text \"t\" locator \"l\"\n",
            "a.r",
            "P",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\npred a.Q : a.公民 → Prop\n\
             rule a.r :\n  params p : a.公民\n  premise a.P p\n  conclude Q p\n\
             \x20 source text \"t\" locator \"l\"\n",
            "a.r",
            "Q",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\npred a.Q : a.公民 → Prop\n\
             rule a.r :\n  params p : a.公民\n  premise a.P p\n  conclude a.P p\n\
             \x20 unless Q p\n  source text \"t\" locator \"l\"\n",
            "a.r",
            "Q",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\n\
             rule a.r :\n  params p : a.公民\n  premise a.P p\n  conclude a.P p\n\
             \x20 defeated_by r2\n  source text \"t\" locator \"l\"\n",
            "a.r",
            "r2",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\n\
             rule a.r :\n  params p : a.公民\n  premise a.P p\n  conclude a.P p\n\
             \x20 prefer r2\n  source text \"t\" locator \"l\"\n",
            "a.r",
            "r2",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\npred a.Q : a.公民 → Prop\n\
             contrary a.P Q\n",
            "contrary a.P Q",
            "Q",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\nunique P 1\n",
            "unique P 1",
            "P",
        ),
        (
            "namespace a\npred a.P : Prop\npred a.Q : Prop\ninterpret a.i : P → a.Q\n",
            "a.i",
            "P",
        ),
        (
            "namespace a\nsort a.公民\npred a.P : a.公民 → Prop\n\
             def a.f : a.公民 → Prop := λ (x : a.公民) := P x\n",
            "a.f",
            "P",
        ),
    ];

    for (src, declaration, name) in cases {
        let err = load(src).expect_err("an unqualified reference must be refused");
        assert!(
            err.contains(declaration),
            "error should name the declaration {declaration}: {err}"
        );
        assert!(
            err.contains(name),
            "error should name the unqualified reference {name}: {err}"
        );
    }
}

#[test]
fn local_binders_do_not_need_a_namespace_prefix() {
    let src = r#"
namespace a
sort a.公民
pred a.P : a.公民 → Prop
pred a.Q : a.公民 → Prop
pred a.R : a.公民 → Prop

rule a.r :
  params p : a.公民
  premise h : a.P p
  premise a.Q p
  conclude a.R p
  unless a.R p
  source text "测试" locator "一"

def a.f : a.公民 → Prop := λ (x : a.公民) := a.P x

axiom a.总 : ∀ (x : a.公民), a.P x → a.P x
  source text "测试" locator "二"
"#;
    let lib = load(src).expect("local binders must not require a prefix");
    assert!(lib.env.get("a.r").is_some());
    assert!(lib.env.get("a.f").is_some());
}

#[test]
fn a_qualified_reference_to_an_earlier_module_loads() {
    let mut lib = Library::new();
    lib.load("a", MODULE_A).expect("a loads");
    let b_uses_a = r#"
namespace b
rule b.借用a :
  params p : a.公民, h : a.住宅
  premise a.非法搜查 p h
  conclude a.不受侵犯 p h
  source text "测试" locator "二"
"#;
    lib.load("b", b_uses_a)
        .expect("a qualified reference to a loaded module is allowed");
    assert!(lib.env.get("b.借用a").is_some());
}

#[test]
fn an_unloaded_qualified_reference_is_an_unknown_name() {
    let err = load("namespace c\nsort c.公民\npred c.P : missing.Sort → Prop\n")
        .expect_err("an unloaded namespace must not resolve")
        .to_string();
    assert!(err.contains("未知名称"), "got: {err}");
    assert!(err.contains("missing.Sort"), "got: {err}");
}

#[test]
fn a_duplicate_kernel_name_is_still_rejected() {
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A)
        .expect("the first load succeeds");
    let before = lib.env.len();
    let err = lib
        .load("a-again.std", MODULE_A)
        .expect_err("a duplicate declaration must not overwrite the first one")
        .to_string();
    assert!(err.contains("名称已被占用"), "got: {err}");
    assert!(err.contains("a.公民"), "got: {err}");
    assert_eq!(
        lib.env.len(),
        before,
        "the failed reload changed the ledger"
    );
}

#[test]
fn a_file_without_a_namespace_keeps_the_old_theory_name_and_names() {
    let mut lib = Library::new();
    lib.load("case.std", "sort 公民\n")
        .expect("a case file loads");
    let theory = lib
        .theory("case.std")
        .expect("the load path names the theory");
    assert_eq!(theory.name, "case.std");
    assert_eq!(theory.namespace, None);
    assert!(lib.env.get("公民").is_some());
}
