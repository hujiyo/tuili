//! Rendering a certificate: the tree a user sees must be the certificate's
//! own tree, including its labels, sources, bindings, gaps and errors.

use std_deduce_cert::{
    render, Assumption, Binding, CertExpr, Certificate, FormatVersion, GapCandidate, Node, Source,
};
use std_deduce_kernel::env::SourceRef;

fn constant(name: &str) -> CertExpr {
    CertExpr::Const {
        name: name.to_owned(),
    }
}

fn app(func: CertExpr, arg: CertExpr) -> CertExpr {
    CertExpr::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

fn atom(predicate: &str, object: &str) -> CertExpr {
    app(constant(predicate), constant(object))
}

fn source(text: &str, locator: &str, version: &str, note: &str) -> Source {
    Source {
        text: text.to_owned(),
        locator: locator.to_owned(),
        version: version.to_owned(),
        effective: None,
        note: note.to_owned(),
        quote: String::new(),
        url: String::new(),
        jurisdiction: String::new(),
        retrieved_at: String::new(),
        hash: String::new(),
    }
}

fn assumption(proposition: CertExpr, sources: Vec<Source>, label: Option<&str>) -> Assumption {
    Assumption {
        proposition,
        sources,
        label: label.map(str::to_owned),
    }
}

fn binding(parameter: &str, value: CertExpr) -> Binding {
    Binding {
        parameter: parameter.to_owned(),
        value,
    }
}

fn certificate(assumptions: Vec<Assumption>, nodes: Vec<Node>, root: Option<usize>) -> Certificate {
    Certificate {
        format_version: FormatVersion::CURRENT,
        assumptions,
        nodes,
        root,
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

fn rule(
    rule: &str,
    conclusion: CertExpr,
    premises: Vec<usize>,
    bindings: Vec<Binding>,
    sources: Vec<Source>,
) -> Node {
    Node::RuleApplication {
        rule: rule.to_owned(),
        conclusion,
        premises,
        bindings,
        sources,
    }
}

#[test]
fn renders_a_rule_tree_with_labels_sources_and_bindings() {
    let certificate = certificate(
        vec![
            assumption(
                atom("侵占", "张三"),
                vec![source("民法典", "第一条", "2020", "")],
                Some("事实一"),
            ),
            assumption(
                atom("侵占", "李四"),
                vec![source("申请人", "材料", "2024", "")],
                None,
            ),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
            rule(
                "规则甲",
                atom("违法", "张三"),
                vec![0, 1],
                vec![
                    binding("p", constant("张三")),
                    binding("q", constant("李四")),
                ],
                vec![source("宪法", "第三十九条", "2018", "按通常理解")],
            ),
        ],
        Some(2),
    );

    let expected = "\
▸ 违法 张三  ⟨规则甲⟩ ← 「宪法第三十九条」（2018）
  注：按通常理解
  实例：p ↦ 张三，q ↦ 李四
  · 侵占 张三  [事实一]  ← 「民法典第一条」（2020）
  · 侵占 李四  ← 「申请人材料」（2024）
";
    assert_eq!(render(&certificate).unwrap(), expected);
}

#[test]
fn renders_a_gap_with_candidates_and_blockers() {
    let certificate = certificate(
        Vec::new(),
        vec![Node::Gap {
            proposition: atom("可复议", "甲"),
            note: Some("目标处于冲突中".to_owned()),
            candidates: vec![
                GapCandidate {
                    rule: "规则一".to_owned(),
                    missing: vec![atom("不批准", "甲"), atom("批准", "甲")],
                    blocked_by: vec![atom("已决", "甲")],
                    sources: vec![source("来源", "一", "", "")],
                },
                GapCandidate {
                    rule: "规则二".to_owned(),
                    missing: Vec::new(),
                    blocked_by: Vec::new(),
                    sources: Vec::new(),
                },
            ],
        }],
        Some(0),
    );

    let expected = "\
? 可复议 甲  【未闭合】
  目标处于冲突中
  候选 ⟨规则一⟩ ← 「来源一」
    缺：不批准 甲；批准 甲
    被阻断：「已决 甲」已成立
  候选 ⟨规则二⟩
";
    assert_eq!(render(&certificate).unwrap(), expected);
}

#[test]
fn without_a_root_prints_unused_nodes_then_gaps_separated_by_blank_lines() {
    let certificate = certificate(
        vec![
            assumption(atom("侵占", "张三"), Vec::new(), None),
            assumption(atom("侵占", "李四"), Vec::new(), None),
        ],
        vec![
            Node::Assumption { assumption: 0 },
            Node::Assumption { assumption: 1 },
            rule(
                "规则甲",
                atom("违法", "张三"),
                vec![0],
                vec![binding("p", constant("张三"))],
                Vec::new(),
            ),
            Node::Gap {
                proposition: atom("可复议", "甲"),
                note: None,
                candidates: Vec::new(),
            },
        ],
        None,
    );

    let expected = "\
· 侵占 李四

▸ 违法 张三  ⟨规则甲⟩
  实例：p ↦ 张三
  · 侵占 张三

? 可复议 甲  【未闭合】
";
    assert_eq!(render(&certificate).unwrap(), expected);
}

#[test]
fn source_one_line_matches_the_kernel_format() {
    let unversioned = source("宪法", "第三十九条", "", "");
    assert_eq!(unversioned.one_line(), "「宪法第三十九条」");
    assert_eq!(
        unversioned.one_line(),
        SourceRef::from(&unversioned).one_line()
    );

    let versioned = source("宪法", "第三十九条", "2018", "");
    assert_eq!(versioned.one_line(), "「宪法第三十九条」（2018）");
    assert_eq!(versioned.one_line(), SourceRef::from(&versioned).one_line());
}

#[test]
fn out_of_range_root_is_an_error_naming_the_node() {
    let certificate = certificate(Vec::new(), Vec::new(), Some(5));
    let error = render(&certificate).expect_err("an out-of-range root cannot be rendered");
    assert!(error.contains("节点 5"), "{error}");
    assert!(error.contains("根节点索引越界"), "{error}");
}

#[test]
fn out_of_range_assumption_index_is_an_error_naming_the_node() {
    let certificate = certificate(
        vec![assumption(atom("侵占", "张三"), Vec::new(), None)],
        vec![Node::Assumption { assumption: 3 }],
        Some(0),
    );
    let error = render(&certificate).expect_err("an unknown assumption cannot be rendered");
    assert!(error.contains("节点 0"), "{error}");
    assert!(error.contains("不存在的假设 3"), "{error}");
}

#[test]
fn out_of_range_premise_is_an_error_naming_the_node() {
    let certificate = certificate(
        Vec::new(),
        vec![rule(
            "规则甲",
            atom("违法", "张三"),
            vec![3],
            Vec::new(),
            Vec::new(),
        )],
        Some(0),
    );
    let error = render(&certificate).expect_err("an out-of-range premise cannot be rendered");
    assert!(error.contains("节点 0"), "{error}");
    assert!(error.contains("前提 3"), "{error}");
}

#[test]
fn a_cycle_reachable_from_the_root_is_an_error() {
    let certificate = certificate(
        Vec::new(),
        vec![
            rule(
                "规则甲",
                atom("违法", "张三"),
                vec![1],
                Vec::new(),
                Vec::new(),
            ),
            rule(
                "规则乙",
                atom("侵占", "张三"),
                vec![0],
                Vec::new(),
                Vec::new(),
            ),
        ],
        Some(0),
    );
    let error = render(&certificate).expect_err("a cyclic node graph cannot be rendered");
    assert!(error.contains("节点图成环"), "{error}");
    assert!(error.contains("0 → 1 → 0"), "{error}");
}

#[test]
fn a_cycle_without_a_root_is_still_an_error() {
    // With no root neither node is printed as a root (each is a premise of the
    // other), so the cycle is caught by the graph validation, not by
    // recursion that would otherwise never be entered.
    let certificate = certificate(
        Vec::new(),
        vec![
            rule(
                "规则甲",
                atom("违法", "张三"),
                vec![1],
                Vec::new(),
                Vec::new(),
            ),
            rule(
                "规则乙",
                atom("侵占", "张三"),
                vec![0],
                Vec::new(),
                Vec::new(),
            ),
        ],
        None,
    );
    let error = render(&certificate).expect_err("a cyclic node graph cannot be rendered");
    assert!(error.contains("节点图成环"), "{error}");
}
