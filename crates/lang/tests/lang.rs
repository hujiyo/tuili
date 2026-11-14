use std_deduce_lang::Library;

#[test]
fn minimal_rule_loads() {
    let src = r#"
sort 公民
pred 非法搜查 : 公民 → 公民 → Prop
obj 张三 : 公民
axiom 事实 : 非法搜查 张三 张三

rule 规则 :
  params p : 公民, h : 公民
  premise 非法搜查 p h
  conclude 非法搜查 p h
  source 测试 一
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
