use std_deduce_lang::parser::parse;
use std_deduce_lang::Library;

#[test]
fn minimal_rule_loads() {
    let src = r#"
sort 公民
pred 非法搜查 : 公民 → 公民 → Prop
obj 张三 : 公民
axiom 事实 : 非法搜查 张三 张三
  source text "测试" locator "夹具"

rule 规则 :
  params p : 公民, h : 公民
  premise 非法搜查 p h
  conclude 非法搜查 p h
  source text "测试" locator "一"
"#;
    let mut lib = Library::new();
    match lib.load("t", src) {
        Ok(r) => println!("ok: {:?}", r.declared),
        Err(e) => panic!("load failed: {e}"),
    }
}

/// A parse error carries its 1-based line and column structurally. The message
/// itself stays free of the location, which the CLI renders in Lean style.
#[test]
fn a_parse_error_keeps_its_line_and_column_out_of_the_message() {
    let err = Library::new()
        .load("bad.std", "sort 公民\nbogus\n")
        .expect_err("an unknown declaration keyword must fail to parse");
    assert_eq!(err.position(), Some((2, 1)), "got: {err}");
    assert_eq!(
        err.render("bad.std"),
        "bad.std:2:1: error: 未知声明关键字 `bogus`"
    );
    assert_eq!(err.to_string(), "未知声明关键字 `bogus`");
    assert!(
        !err.to_string().contains("第 2 行"),
        "the message must not embed the position: {err}"
    );
}

#[test]
fn contrary_declaration_loads() {
    let src = r#"
sort 申请
pred 该批准 : 申请 → Prop
pred 不该批准 : 申请 → Prop
contrary 该批准 不该批准
"#;
    let mut lib = Library::new();
    lib.load("t", src)
        .expect("contrary declaration should load");
    assert_eq!(lib.env.contrary_pairs().len(), 1);
}

/// A parameter and a premise binder with the same name would both be opened
/// as `?p`, so the reasoner could not tell a premise proof from a parameter
/// value. Loading must refuse the rule.
#[test]
fn duplicate_param_and_premise_binder_is_rejected() {
    let src = r#"
pred R : Prop → Prop
pred P : Prop
pred Q : Prop → Prop

rule 重名 :
  params p : Prop
  premise r : R p
  premise p : P
  conclude Q p
  source text "测试" locator "夹具"
"#;
    let mut lib = Library::new();
    let err = lib
        .load("t", src)
        .expect_err("a duplicate parameter/premise binder must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("binder `p`") && msg.contains("?p"),
        "error should name the duplicated binder `p`, got: {msg}"
    );
}

/// An unnamed premise gets the generated binder `_p{i}`; a parameter with
/// that name collides with it in the opened rule.
#[test]
fn duplicate_generated_premise_binder_is_rejected() {
    let src = r#"
pred P : Prop
pred Q : Prop

rule 重名 :
  params _p0 : Prop
  premise P
  conclude P
  source text "测试" locator "夹具"
"#;
    let mut lib = Library::new();
    let err = lib
        .load("t", src)
        .expect_err("a parameter colliding with a generated premise binder must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("binder `_p0`") && msg.contains("?_p0"),
        "error should name the duplicated generated binder `_p0`, got: {msg}"
    );
}

/// A parameter that appears only in an `unless` condition is not fixed when
/// the rule fires: a certificate could pick a binding of its own to dodge the
/// blocker, so loading must refuse the rule.
#[test]
fn parameter_only_in_unless_is_rejected() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"
axiom 无辜事实 : 无辜 张三
  source text "测试" locator "夹具"

rule r :
  params p : 公民, q : 公民 → Prop
  premise 侵占 p
  conclude 违法 p
  unless q 张三
  source text "测试" locator "夹具"
"#;
    let mut lib = Library::new();
    let err = lib
        .load("t", src)
        .expect_err("a parameter only in an unless condition must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("参数 `q`") && msg.contains("没有出现在任何前提里") && msg.contains("unless"),
        "error should name the unconstrained parameter `q` and its unless clause, got: {msg}"
    );
}

/// A rule is an assertion bridge and must name its source; the load error
/// names the declaration so the missing provenance can be fixed.
#[test]
fn a_rule_without_a_source_is_rejected_and_the_error_names_it() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民

rule 无来源规则 :
  params p : 公民
  premise 侵占 p
  conclude 侵占 p
"#;
    let err = Library::new()
        .load("t", src)
        .expect_err("a rule without a source must be refused")
        .to_string();
    assert!(err.contains("无来源规则"), "got: {err}");
    assert!(err.contains("缺少 source"), "got: {err}");

    let with_source = format!("{src}  source text \"测试\" locator \"夹具\"\n");
    Library::new()
        .load("t", &with_source)
        .expect("the same rule loads once it has a source");
}

#[test]
fn an_axiom_without_a_source_is_rejected_and_the_error_names_it() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民

axiom 无来源事实 : 侵占 张三
"#;
    let err = Library::new()
        .load("t", src)
        .expect_err("an axiom without a source must be refused")
        .to_string();
    assert!(err.contains("无来源事实"), "got: {err}");
    assert!(err.contains("缺少 source"), "got: {err}");

    let with_source = format!("{src}  source text \"测试\" locator \"夹具\"\n");
    Library::new()
        .load("t", &with_source)
        .expect("the same axiom loads once it has a source");
}

/// A source made only of whitespace names nothing: it must be rejected just
/// like a missing one, not printed as `「  」`.
#[test]
fn a_rule_with_a_blank_source_is_rejected() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民

rule 空白来源规则 :
  params p : 公民
  premise 侵占 p
  conclude 侵占 p
  source text " " locator " "
"#;
    let err = Library::new()
        .load("t", src)
        .expect_err("a blank rule source must be refused")
        .to_string();
    assert!(err.contains("空白来源规则"), "got: {err}");
    assert!(err.contains("空白"), "got: {err}");
}

#[test]
fn an_axiom_with_a_blank_source_is_rejected() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民

axiom 空白来源事实 : 侵占 张三
  source text " " locator " "
"#;
    let err = Library::new()
        .load("t", src)
        .expect_err("a blank axiom source must be refused")
        .to_string();
    assert!(err.contains("空白来源事实"), "got: {err}");
    assert!(err.contains("空白"), "got: {err}");
}

/// The source check runs before elaboration: a rule that would also fail to
/// elaborate must report the missing source, naming the rule, not a type or
/// name-resolution error.
#[test]
fn a_missing_source_is_reported_before_a_premise_that_does_not_elaborate() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
obj 张三 : 公民

rule 缺来源坏前提 :
  params p : 公民
  premise 不存在的谓词 p
  conclude 侵占 p
"#;
    let err = Library::new()
        .load("t", src)
        .expect_err("the rule must be refused")
        .to_string();
    assert!(err.contains("缺来源坏前提"), "got: {err}");
    assert!(err.contains("缺少 source"), "got: {err}");
    assert!(
        !err.contains("未知名称") && !err.contains("不是命题"),
        "the missing source must win over the elaboration error, got: {err}"
    );
}

/// A failed load works on a clone and commits nothing: neither the new
/// declarations nor the theory may appear in the library.
#[test]
fn a_failed_load_leaves_the_library_unchanged() {
    let mut lib = Library::new();
    lib.load("base", "sort 公民\npred 侵占 : 公民 → Prop\n")
        .expect("the base theory loads");
    let before = lib.env.len();

    let bad = r#"
sort 住宅
pred 违法 : 公民 → Prop
rule 坏规则 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
"#;
    let err = lib.load("bad", bad).unwrap_err().to_string();
    assert!(
        err.contains("坏规则") && err.contains("缺少 source"),
        "got: {err}"
    );
    assert_eq!(
        lib.env.len(),
        before,
        "the failed load must add no declaration"
    );
    assert!(
        lib.env.get("住宅").is_none(),
        "a partial declaration leaked"
    );
    assert!(
        lib.theory("bad").is_none(),
        "the failed theory was recorded"
    );
}

/// Type, vocabulary and definition declarations are not assertions: they are
/// exempt from the source requirement, and so are the conflict declarations
/// whose provenance is checked by a later layer.
#[test]
fn type_vocabulary_definition_conflict_and_unique_declarations_need_no_source() {
    let src = r#"
sort 公民
obj 张三 : 公民
pred 侵占 : 公民 → Prop
pred 合法 : 公民 → Prop
def 侵权 : 公民 → Prop := λ (x : 公民) := 侵占 x
contrary 侵占 合法
unique 侵占 1
"#;
    Library::new()
        .load("t", src)
        .expect("exempt declarations must load without a source");
}

/// A parameter used nowhere is never bound by the reasoner, while the
/// certificate checker demands a binding for every parameter. Loading must
/// refuse such a rule instead of letting the two disagree.
#[test]
fn unused_parameter_is_rejected() {
    let src = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
rule r :
  params p : 公民, q : 公民
  premise 侵占 p
  conclude 违法 p
  source text "测试" locator "夹具"
"#;
    let mut lib = Library::new();
    let err = lib
        .load("t", src)
        .expect_err("a parameter used nowhere must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("参数 `q`") && msg.contains("没有出现在任何前提里") && msg.contains("空参数"),
        "error should name the empty parameter `q`, got: {msg}"
    );
}

/// `#proposition` checks that its term is a proposition; it never proves it.
/// Both the sigiled and the bare spelling are accepted, like `#check`.
#[test]
fn proposition_checks_a_prop_in_both_spellings() {
    let src = r#"
sort 公民
obj 张三 : 公民
pred 侵占 : 公民 → Prop

#proposition 侵占 张三
proposition 侵占 张三
"#;
    let mut lib = Library::new();
    let report = lib.load("t", src).expect("a proposition check must load");
    assert_eq!(
        report.checked,
        vec!["命题：侵占 张三", "命题：侵占 张三"],
        "each spelling must confirm the term is a proposition"
    );
}

/// A command is an item like any other: a rule block ends before it and the
/// command is still parsed as a command.
#[test]
fn proposition_may_follow_a_rule_block() {
    let src = r#"
sort 公民
obj 张三 : 公民
pred 侵占 : 公民 → Prop

rule 恒真 :
  params p : 公民
  premise 侵占 p
  conclude 侵占 p
  source text "测试" locator "夹具"

#proposition 侵占 张三
"#;
    let mut lib = Library::new();
    let report = lib
        .load("t", src)
        .expect("a command may follow a rule block");
    assert_eq!(report.checked.len(), 1, "{:?}", report.checked);
    assert!(
        report.checked[0].contains("命题：侵占 张三"),
        "{:?}",
        report.checked
    );
}

#[test]
fn proposition_rejects_a_non_proposition() {
    let src = r#"
sort 公民
obj 张三 : 公民
#proposition 张三
"#;
    let err = Library::new()
        .load("t", src)
        .expect_err("an individual is not a proposition")
        .to_string();
    assert!(err.contains("`#proposition`"), "{err}");
    assert!(err.contains("不是命题"), "{err}");
}

/// The old `#assert` must fail at the command itself and explain the rename.
#[test]
fn assert_reports_the_rename_at_the_command_position() {
    let error = parse("sort 公民\n  #assert 公民\n").expect_err("`#assert` must be rejected");
    assert_eq!((error.line, error.col), (2, 3), "{error}");
    assert!(error.msg.contains("`#assert` 已改名"), "{error}");
    assert!(error.msg.contains("`#proposition`"), "{error}");
    assert!(error.msg.contains("不证明命题成立"), "{error}");
    assert!(
        error.msg.contains("事实") && error.msg.contains("规则"),
        "{error}"
    );

    let bare = parse("sort 公民\nassert 公民\n").expect_err("bare `assert` must be rejected");
    assert_eq!((bare.line, bare.col), (2, 1), "{bare}");
    assert!(bare.msg.contains("`#assert` 已改名"), "{bare}");
}

/// `#check` and `#show` keep their behavior after the rename.
#[test]
fn check_and_show_keep_their_behavior() {
    let src = r#"
sort 公民
obj 张三 : 公民
pred 侵占 : 公民 → Prop

#check 侵占 张三
show 侵占
"#;
    let mut lib = Library::new();
    let report = lib.load("t", src).expect("check and show must load");
    assert_eq!(report.checked, vec!["侵占 张三 : Prop"]);
    assert!(
        report
            .shown
            .iter()
            .any(|line| line.starts_with("侵占 :") && line.contains("→ Prop")),
        "{:?}",
        report.shown
    );
}
