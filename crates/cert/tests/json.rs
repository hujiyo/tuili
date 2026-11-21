//! JSON round-trip and schema-stability tests for certificates.

use serde_json::Value;
use std_deduce_cert::{
    Assumption, Binding, CertExpr, Certificate, Conflict, FormatVersion, GapCandidate, Metadata,
    Node, ObligationKind, OpenObligation, Provenance, Resolution, Side, Source,
};
use std_deduce_kernel::env::SourceRef;
use std_deduce_kernel::{name, Expr};

const SNAPSHOT: &str = include_str!("fixtures/certificate_v1.json");

fn constant(text: &str) -> CertExpr {
    CertExpr::Const {
        name: text.to_owned(),
    }
}

fn app(func: CertExpr, arg: CertExpr) -> CertExpr {
    CertExpr::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

fn source(text: &str, locator: &str) -> Source {
    Source {
        text: text.to_owned(),
        locator: locator.to_owned(),
        version: "2020年修正".to_owned(),
        effective: Some("2021-03-01".to_owned()),
        note: "按现行条文形式化".to_owned(),
    }
}

fn sample_certificate() -> Certificate {
    let defence = app(constant("不法侵害"), constant("张三"));
    let justified = app(constant("不负刑事责任"), constant("张三"));
    Certificate {
        format_version: FormatVersion::CURRENT,
        assumptions: vec![Assumption {
            proposition: defence.clone(),
            sources: vec![source(
                "为了使国家、公共利益、本人或者他人的人身、财产和其他权利免受正在进行的不法侵害，而采取的制止不法侵害的行为，对不法侵害人造成损害的，属于正当防卫，不负刑事责任。",
                "中华人民共和国刑法第二十条第一款",
            )],
            label: Some("事实：不法侵害正在进行".to_owned()),
        }],
        nodes: vec![
            Node::Assumption { assumption: 0 },
            Node::RuleApplication {
                rule: "正当防卫".to_owned(),
                conclusion: justified.clone(),
                premises: vec![0],
                bindings: vec![Binding {
                    parameter: "p".to_owned(),
                    value: constant("张三"),
                }],
                sources: vec![source(
                    "正当防卫，不负刑事责任",
                    "中华人民共和国刑法第二十条第一款",
                )],
            },
            Node::Gap {
                proposition: app(constant("赔偿"), constant("张三")),
                candidates: vec![GapCandidate {
                    rule: "侵权赔偿".to_owned(),
                    missing: vec![app(constant("损害"), constant("张三"))],
                    blocked_by: Vec::new(),
                    sources: vec![source(
                        "行为人因过错侵害他人民事权益造成损害的，应当承担侵权责任。",
                        "中华人民共和国民法典第一千一百六十五条",
                    )],
                }],
                note: Some("缺少损害事实".to_owned()),
            },
        ],
        root: Some(1),
        conflicts: vec![Conflict {
            left: justified,
            right: app(constant("应负刑事责任"), constant("张三")),
            left_by: Provenance::Rules {
                rules: vec!["正当防卫".to_owned()],
            },
            right_by: Provenance::Assumption,
            resolution: Resolution::Defeated { winner: Side::Left },
        }],
        open_obligations: vec![OpenObligation {
            id: "obligation-1".to_owned(),
            kind: ObligationKind::NeedsHumanDetermination,
            description: "「不法侵害」是否达到法定程度需要人判断".to_owned(),
            nodes: vec![1],
        }],
        metadata: Metadata {
            generated_at: Some("2026-11-21T12:00:00Z".to_owned()),
            tool: Some("std-deduce".to_owned()),
            tool_version: Some("0.1.0".to_owned()),
        },
    }
}

#[test]
fn serialization_round_trips_and_is_stable() {
    let certificate = sample_certificate();

    let pretty = certificate.to_json_pretty().unwrap();
    let parsed = Certificate::from_json(&pretty).unwrap();
    assert_eq!(certificate, parsed);
    assert_eq!(pretty, parsed.to_json_pretty().unwrap());

    let compact = certificate.to_json().unwrap();
    let parsed = Certificate::from_json(&compact).unwrap();
    assert_eq!(certificate, parsed);
    assert_eq!(compact, parsed.to_json().unwrap());
}

#[test]
fn snapshot_matches_fixture() {
    let actual = sample_certificate().to_json_pretty().unwrap();
    let expected = SNAPSHOT.replace("\r\n", "\n");
    assert_eq!(actual, expected.trim_end_matches('\n'));
}

#[test]
fn field_names_are_stable() {
    let value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    let object = value.as_object().expect("certificate is a JSON object");
    let expected = [
        "assumptions",
        "conflicts",
        "format_version",
        "metadata",
        "nodes",
        "open_obligations",
        "root",
    ];
    assert_eq!(object.len(), expected.len());
    for field in expected {
        assert!(object.contains_key(field), "missing field `{field}`");
    }

    assert_eq!(value["format_version"], 1);
    assert_eq!(value["nodes"][0]["kind"], "assumption");
    assert_eq!(value["nodes"][1]["kind"], "rule_application");
    assert_eq!(value["nodes"][2]["kind"], "gap");
    assert_eq!(value["nodes"][1]["bindings"][0]["parameter"], "p");
    assert_eq!(
        value["assumptions"][0]["sources"][0]["locator"],
        "中华人民共和国刑法第二十条第一款"
    );
    assert_eq!(value["conflicts"][0]["left_by"]["kind"], "rules");
    assert_eq!(value["conflicts"][0]["resolution"]["kind"], "defeated");
    assert_eq!(value["conflicts"][0]["resolution"]["winner"], "left");
    assert_eq!(
        value["open_obligations"][0]["kind"],
        "needs_human_determination"
    );
}

#[test]
fn unknown_format_version_is_rejected() {
    let text = SNAPSHOT.replace("\"format_version\": 1", "\"format_version\": 999");
    let error = Certificate::from_json(&text).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("unsupported certificate format version 999"),
        "{error}"
    );
}

#[test]
fn missing_format_version_is_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value
        .as_object_mut()
        .unwrap()
        .remove("format_version")
        .expect("fixture has a format_version");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("missing field `format_version`"),
        "{error}"
    );
}

#[test]
fn unknown_fields_are_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value
        .as_object_mut()
        .unwrap()
        .insert("future_field".to_owned(), Value::Bool(true));
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("unknown field `future_field`"),
        "{error}"
    );
}

#[test]
fn unknown_node_fields_are_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["nodes"][0]["future_node_field"] = Value::Bool(true);
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(error.to_string().contains("unknown field"), "{error}");
}

#[test]
fn unknown_expression_fields_are_rejected() {
    let text = SNAPSHOT.replacen(
        "\"kind\": \"const\"",
        "\"kind\": \"const\", \"future_field\": true",
        1,
    );
    let error = Certificate::from_json(&text).unwrap_err();
    assert!(error.to_string().contains("unknown field"), "{error}");
}

#[test]
fn sources_and_bindings_survive_round_trip() {
    let certificate = Certificate::from_json(SNAPSHOT).unwrap();
    let assumption = &certificate.assumptions[0];
    assert_eq!(
        assumption.sources[0].locator,
        "中华人民共和国刑法第二十条第一款"
    );
    assert_eq!(
        assumption.sources[0].effective.as_deref(),
        Some("2021-03-01")
    );

    let Node::RuleApplication {
        bindings, sources, ..
    } = &certificate.nodes[1]
    else {
        panic!("node 1 is not a rule application");
    };
    assert_eq!(
        bindings,
        &[Binding {
            parameter: "p".to_owned(),
            value: constant("张三"),
        }]
    );
    assert_eq!(sources[0].locator, "中华人民共和国刑法第二十条第一款");
}

#[test]
fn kernel_expr_round_trips_through_cert_expr() {
    let expr = Expr::Let {
        name: Some(name("x")),
        value: Box::new(Expr::Lam {
            name: None,
            domain: Box::new(Expr::constant("公民")),
            body: Box::new(Expr::var(0)),
        }),
        body: Box::new(Expr::Pi {
            name: Some(name("y")),
            domain: Box::new(Expr::var(1)),
            codomain: Box::new(Expr::App {
                func: Box::new(Expr::var(0)),
                arg: Box::new(Expr::Sort(0)),
            }),
        }),
    };

    let dto = CertExpr::try_from(&expr).unwrap();
    let json = serde_json::to_string_pretty(&dto).unwrap();
    let decoded: CertExpr = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded, dto);
    assert_eq!(Expr::from(&decoded), expr);
    assert_eq!(CertExpr::try_from(expr.clone()).unwrap(), dto);
}

#[test]
fn anonymous_binders_are_explicit_null_fields() {
    let dto = CertExpr::Pi {
        binder: None,
        domain: Box::new(CertExpr::Sort { level: 0 }),
        codomain: Box::new(CertExpr::Var { index: 0 }),
    };
    let value = serde_json::to_value(&dto).unwrap();
    let object = value.as_object().unwrap();
    assert!(object.contains_key("binder"));
    assert!(object["binder"].is_null());
    assert_eq!(object["kind"], "pi");
}

#[test]
fn de_bruijn_index_that_does_not_fit_is_rejected() {
    if usize::BITS > 32 {
        let index = u32::MAX as usize + 1;
        let error = CertExpr::try_from(&Expr::var(index)).unwrap_err();
        assert_eq!(error.index, index);
    }
}

#[test]
fn kernel_source_ref_round_trips() {
    let source = source("条文原文", "刑法第二十条");
    let kernel = SourceRef::from(source.clone());
    assert_eq!(Source::from(&kernel), source);
}
