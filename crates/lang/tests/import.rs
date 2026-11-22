//! Imports: a file names the packages it builds on before its namespace and
//! its declarations. The parser owns the ordering; the library only checks
//! that each imported namespace is already loaded in this session.

use std_deduce_lang::ast::Item;
use std_deduce_lang::parser::parse;
use std_deduce_lang::Library;

const MODULE_A: &str = r#"
namespace a
sort a.公民
pred a.非法搜查 : a.公民 → Prop
"#;

const MODULE_B: &str = r#"
namespace b
sort b.公民
"#;

const MODULE_B_IMPORTS_A: &str = r#"
import a
namespace b
sort b.公民
pred b.借用 : a.公民 → Prop
"#;

// ---------------- parser ----------------

#[test]
fn imports_may_precede_the_namespace_and_declarations() {
    let items = parse("import a\n\nimport b\nnamespace x\nsort x.公民\n")
        .expect("imports before the namespace must parse");
    assert_eq!(items[0], Item::Import("a".into()));
    assert_eq!(items[1], Item::Import("b".into()));
    assert_eq!(items[2], Item::Namespace("x".into()));
    match &items[3] {
        Item::Sort { name, .. } => assert_eq!(name, "x.公民"),
        other => panic!("expected a sort, got {other:?}"),
    }

    // A case file may import too, with no namespace at all.
    let items = parse("import a\nsort 公民\n").expect("a case file may import");
    assert_eq!(items[0], Item::Import("a".into()));
    assert!(matches!(items[1], Item::Sort { .. }));

    // A file may consist of imports only.
    assert_eq!(parse("import a").expect("import at EOF parses").len(), 1);
}

#[test]
fn imports_after_the_namespace_or_a_declaration_are_rejected() {
    for src in [
        "namespace x\nimport a\n",
        "sort 公民\nimport a\n",
        "namespace x\nsort x.公民\nimport a\n",
        "#check Prop\nimport a\n",
    ] {
        let err = parse(src).expect_err("an import after the header or a declaration must fail");
        assert!(
            err.to_string().contains("import 只能出现在"),
            "for {src:?}, got: {err}"
        );
    }

    // The diagnostic points at the misplaced import, not at the file start.
    let err = parse("namespace x\nimport a\n").expect_err("import after namespace");
    assert_eq!((err.line, err.col), (2, 1), "{err}");
}

#[test]
fn a_bare_import_reports_the_import_line() {
    for (src, line) in [
        ("import\nsort a\n", 1),
        ("\n\nimport\nsort a\n", 3),
        ("import", 1),
    ] {
        let err = parse(src).expect_err("an import without a package must fail");
        assert_eq!(err.line, line, "for {src:?}, got: {err}");
        assert_eq!(err.col, 1, "for {src:?}, got: {err}");
        assert!(
            err.to_string().contains("必须是包名"),
            "for {src:?}, got: {err}"
        );
    }
}

#[test]
fn tokens_after_an_import_on_the_same_line_are_rejected() {
    for src in ["import a b\n", "import a,\n", "import a b"] {
        let err = parse(src).expect_err("an import takes exactly one package");
        assert!(
            err.to_string().contains("必须是换行"),
            "for {src:?}, got: {err}"
        );
    }
}

#[test]
fn duplicate_imports_are_kept_for_the_library_to_deduplicate() {
    let items = parse("import a\nimport a\nnamespace x\nsort x.公民\n")
        .expect("a duplicate import is legal at parse time");
    let imports: Vec<&Item> = items
        .iter()
        .filter(|item| matches!(item, Item::Import(_)))
        .collect();
    assert_eq!(imports.len(), 2, "{items:?}");
    assert_eq!(imports[0], &Item::Import("a".into()));
    assert_eq!(imports[1], &Item::Import("a".into()));
}

#[test]
fn an_at_version_on_an_import_is_not_syntax() {
    let err = parse("import cn.constitution@2018\n")
        .expect_err("a version belongs to the lock file, not to the import")
        .to_string();
    assert!(err.contains("无法识别"), "got: {err}");
    assert!(err.contains("'@'"), "got: {err}");
}

#[test]
fn a_second_namespace_is_still_rejected_after_imports() {
    let err = parse("import a\nnamespace x\nnamespace y\n")
        .expect_err("imports do not allow a second namespace")
        .to_string();
    assert!(err.contains("只能出现一次"), "got: {err}");
}

// ---------------- library ----------------

#[test]
fn a_case_file_can_import_a_loaded_namespace() {
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A).expect("a loads");
    let report = lib
        .load("case.std", "import a\nsort 案件类别\n")
        .expect("a loaded namespace may be imported");
    assert_eq!(report.imported, vec!["a".to_string()]);
    assert!(report.declared.iter().any(|name| name == "案件类别"));
    assert!(
        !report.declared.iter().any(|name| name == "a"),
        "an import is not a declaration: {:?}",
        report.declared
    );
    assert!(lib.env.get("a.非法搜查").is_some());
    assert!(lib.env.get("案件类别").is_some());

    let theory = lib.theory("case.std").expect("the case theory exists");
    assert_eq!(theory.namespace, None);
    assert_eq!(theory.requires, vec!["a".to_string()]);
}

#[test]
fn duplicate_imports_are_reported_and_recorded_once() {
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A).expect("a loads");
    let report = lib
        .load("case.std", "import a\nimport a\nsort 案件类别\n")
        .expect("duplicate imports are legal");
    assert_eq!(report.imported, vec!["a".to_string()]);
    assert_eq!(
        lib.theory("case.std").unwrap().requires,
        vec!["a".to_string()]
    );
}

#[test]
fn importing_an_unloaded_namespace_fails_without_changing_the_library() {
    let mut lib = Library::new();
    let before = lib.env.len();
    let err = lib
        .load("case.std", "import a\nsort 案件类别\n")
        .expect_err("an unloaded package must not resolve")
        .to_string();
    assert!(err.contains("`a`"), "got: {err}");
    assert!(err.contains("尚未加载"), "got: {err}");
    assert_eq!(lib.env.len(), before, "the failed load changed the ledger");
    assert!(lib.env.get("案件类别").is_none());
    assert!(
        lib.theory("case.std").is_none(),
        "the failed load left a theory behind"
    );
}

#[test]
fn an_import_needs_a_loaded_namespace_not_merely_a_matching_theory_name() {
    let mut lib = Library::new();
    lib.load("a", "sort 案件\n")
        .expect("a case theory may be named `a` without a namespace");
    let err = lib
        .load("case.std", "import a\nsort 别的案件\n")
        .expect_err("a theory named `a` is not namespace `a`")
        .to_string();
    assert!(
        err.contains("`a`") && err.contains("尚未加载"),
        "got: {err}"
    );
    assert!(lib.env.get("别的案件").is_none());
}

#[test]
fn a_module_may_import_another_loaded_module() {
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A).expect("a loads");
    let report = lib
        .load("b.std", MODULE_B_IMPORTS_A)
        .expect("a module may import a loaded module");
    assert_eq!(report.imported, vec!["a".to_string()]);
    assert_eq!(lib.theory("b").unwrap().requires, vec!["a".to_string()]);
    assert!(lib.env.get("b.借用").is_some());
}

#[test]
fn an_import_may_name_a_dotted_package() {
    let mut lib = Library::new();
    lib.load("ab.std", "namespace a.b\nsort a.b.公民\n")
        .expect("a dotted namespace loads");
    let report = lib
        .load("c.std", "import a.b\nnamespace c\nsort c.公民\n")
        .expect("a dotted package may be imported");
    assert_eq!(report.imported, vec!["a.b".to_string()]);
    assert_eq!(lib.theory("c").unwrap().requires, vec!["a.b".to_string()]);
}

#[test]
fn a_failed_load_does_not_record_imports_or_leak_declarations() {
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A).expect("a loads");
    lib.load("case.std", "sort 案件\n")
        .expect("the case theory loads");
    let before = lib.env.len();

    // The import itself is valid, but the declaration collides. The clone is
    // discarded, so the theory must not acquire the import either.
    let err = lib
        .load("case.std", "import a\nsort 案件\n")
        .expect_err("a duplicate declaration is still rejected")
        .to_string();
    assert!(err.contains("名称已被占用"), "got: {err}");
    assert_eq!(lib.env.len(), before, "the failed load changed the ledger");
    assert!(
        lib.theory("case.std").unwrap().requires.is_empty(),
        "the failed load recorded `a` as a requirement"
    );
}

#[test]
fn theory_requires_accumulates_imports_across_reloads() {
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A).expect("a loads");
    lib.load("b.std", MODULE_B).expect("b loads");
    lib.load("case.std", "import a\nsort 案件一\n")
        .expect("the first file loads");
    let report = lib
        .load("case.std", "import a\nimport b\nsort 案件二\n")
        .expect("the second file loads");
    assert_eq!(
        report.imported,
        vec!["a".to_string(), "b".to_string()],
        "the report lists this file's imports only"
    );
    assert_eq!(
        lib.theory("case.std").unwrap().requires,
        vec!["a".to_string(), "b".to_string()],
        "the merged theory records each package once"
    );
}

#[test]
fn imports_do_not_skip_declaration_name_checks() {
    let mut lib = Library::new();
    lib.load("a.std", MODULE_A).expect("a loads");
    let err = lib
        .load("b.std", "import a\nnamespace b\nsort 公民\n")
        .expect_err("a module declaration still needs the namespace prefix")
        .to_string();
    assert!(err.contains("`b.` 开头"), "got: {err}");

    let err = lib
        .load("case.std", "import a\nsort a.类别\n")
        .expect_err("a case declaration still cannot be dotted")
        .to_string();
    assert!(err.contains("不能声明带"), "got: {err}");
}
