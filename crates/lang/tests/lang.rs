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
