//! JSON round-trip and schema-stability tests for certificates.

use serde_json::Value;
use std_deduce_cert::{
    ApplicabilityBasis, ApplicabilityReason, ApplicabilityReasonKind, ApplicabilityVerdict,
    Assumption, Binding, CertExpr, Certificate, Conflict, CorpusRecord, EnvironmentIdentity,
    EnvironmentRecord, Explicit, ExplicitText, FactIdentity, FormatVersion, GapCandidate,
    Interpretation, InterpretationDirection, Metadata, Node, ObligationKind, OpenObligation,
    PackRecord, PriorityClause, PriorityEdge, PriorityOrigin, Provenance, Resolution,
    ResolutionBasis, RuleApplicability, Side, Source, TrustLevel, UnresolvedReason,
};
use std_deduce_kernel::env::SourceRef;
use std_deduce_kernel::{name, Expr};

const SNAPSHOT: &str = include_str!("fixtures/certificate_v9.json");
const V8_SNAPSHOT: &str = include_str!("fixtures/certificate_v8.json");
const V6_SNAPSHOT: &str = include_str!("fixtures/certificate_v6.json");
const V5_SNAPSHOT: &str = include_str!("fixtures/certificate_v5.json");
const V4_SNAPSHOT: &str = include_str!("fixtures/certificate_v4.json");
const V3_SNAPSHOT: &str = include_str!("fixtures/certificate_v3.json");
const V2_SNAPSHOT: &str = include_str!("fixtures/certificate_v2.json");

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

/// The record of a rule declared without any scope: unchecked because there is
/// nothing to judge, with an empty basis.
/// A gap candidate stores its record inline: the candidate list is already
/// behind a `Vec`.
fn unscoped_candidate_applicability() -> RuleApplicability {
    *unscoped_applicability()
}
fn unscoped_applicability() -> Box<RuleApplicability> {
    Box::new(RuleApplicability {
        verdict: ApplicabilityVerdict::Unchecked,
        basis: ApplicabilityBasis::default(),
        reason: Explicit::some(ApplicabilityReason::new(
            ApplicabilityReasonKind::RuleHasNoScope,
        )),
    })
}

fn source(text: &str, locator: &str) -> Source {
    Source {
        text: text.to_owned(),
        locator: locator.to_owned(),
        version: "2020年修正".to_owned(),
        effective: Some("2021-03-01".to_owned()),
        note: "按现行条文形式化".to_owned(),
        quote: "条文原文".to_owned(),
        url: "https://example.test/law?article=20".to_owned(),
        jurisdiction: "CN".to_owned(),
        retrieved_at: "2026-11-21".to_owned(),
        hash: "sha256:abc".to_owned(),
    }
}

/// Remove the fields added in certificate v2 from every source object, so a
/// test can construct a true v1 payload or a v2 payload written by an older
/// reader.
fn strip_new_source_fields(value: &mut Value) {
    match value {
        Value::Object(object) => {
            if object.contains_key("text") && object.contains_key("locator") {
                for field in ["quote", "url", "jurisdiction", "retrieved_at", "hash"] {
                    object.remove(field);
                }
            }
            for child in object.values_mut() {
                strip_new_source_fields(child);
            }
        }
        Value::Array(items) => {
            for item in items {
                strip_new_source_fields(item);
            }
        }
        _ => {}
    }
}

fn sample_certificate() -> Certificate {
    let defence = app(constant("不法侵害"), constant("张三"));
    let justified = app(constant("不负刑事责任"), constant("张三"));
    let self_defence = app(constant("正当防卫"), constant("张三"));
    Certificate {
        format_version: FormatVersion::CURRENT,
        environment: EnvironmentIdentity::Recorded(EnvironmentRecord {
            profile: ExplicitText::some("cn.default"),
            packs: vec![PackRecord {
                name: "cn.constitution".to_owned(),
                version: "0.4.0".to_owned(),
                hash: format!("sha256:{}", "0123456789abcdef".repeat(4)),
                trust: TrustLevel::Official,
            }],
            corpora: vec![CorpusRecord {
                law: "cn.constitution".to_owned(),
                version: "2018".to_owned(),
                file_sha256: format!("sha256:{}", "abcdef0123456789".repeat(4)),
            }],
            as_of: ExplicitText::none(),
            jurisdiction: ExplicitText::none(),
        }),
        assumptions: vec![Assumption {
            proposition: defence.clone(),
            identity: FactIdentity::UserAsserted,
            sources: vec![source(
                "为了使国家、公共利益、本人或者他人的人身、财产和其他权利免受正在进行的不法侵害，而采取的制止不法侵害的行为，对不法侵害人造成损害的，属于正当防卫，不负刑事责任。",
                "中华人民共和国刑法第二十条第一款",
            )],
            label: Some("事实：不法侵害正在进行".to_owned()),
            occurred_at: Explicit::some("2025-03-01".to_owned()),
            occurred_in: Explicit::some("CN".to_owned()),
        }],
        interpretations: vec![Interpretation {
            id: "防卫解释".to_owned(),
            direction: InterpretationDirection::Expand,
            from: defence.clone(),
            to: self_defence.clone(),
            sources: vec![source("正当防卫的解释", "第一条")],
        }],
        nodes: vec![
            Node::Assumption { assumption: 0 },
            Node::InterpretationApplication {
                interpretation: 0,
                premise: 0,
                conclusion: self_defence,
            },
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
                applicability: unscoped_applicability(),
            },
            Node::Gap {
                proposition: app(constant("赔偿"), constant("张三")),
                axiom_candidates: Vec::new(),
                candidates: vec![GapCandidate {
                    rule: "侵权赔偿".to_owned(),
                    bindings: Vec::new(),
                    held: Vec::new(),
                    missing: vec![app(constant("损害"), constant("张三"))],
                    blocked_by: Vec::new(),
                    sources: vec![source(
                        "行为人因过错侵害他人民事权益造成损害的，应当承担侵权责任。",
                        "中华人民共和国民法典第一千一百六十五条",
                    )],
                    applicability: unscoped_candidate_applicability(),
                }],
                note: Some("缺少损害事实".to_owned()),
            },
        ],
        root: Some(2),
        alternatives: vec![
            std_deduce_cert::Alternative {
                proposition: app(constant("不负刑事责任"), constant("张三")),
                witnesses: vec![2],
                truncated: false,
            },
        ],
        conflicts: vec![Conflict {
            left: justified,
            right: app(constant("应负刑事责任"), constant("张三")),
            left_by: Provenance::Rules {
                rules: vec!["正当防卫".to_owned()],
            },
            right_by: Provenance::Rules {
                rules: vec!["应负刑事责任规则".to_owned()],
            },
            resolution: Resolution::Defeated {
                winner: Side::Left,
                basis: ResolutionBasis::Priority {
                    edges: vec![PriorityEdge {
                        winner: "正当防卫".to_owned(),
                        loser: "应负刑事责任规则".to_owned(),
                        origin: PriorityOrigin::PriorityDeclaration {
                            declared_in: "cn.constitution".to_owned(),
                            sources: vec![source("中华人民共和国立法法", "第九十二条")],
                        },
                    }],
                },
            },
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
        "alternatives",
        "assumptions",
        "conflicts",
        "environment",
        "format_version",
        "interpretations",
        "metadata",
        "nodes",
        "open_obligations",
        "root",
    ];
    assert_eq!(object.len(), expected.len());
    for field in expected {
        assert!(object.contains_key(field), "missing field `{field}`");
    }

    assert_eq!(value["format_version"], 9);
    let environment = value["environment"]
        .as_object()
        .expect("the environment is an inline object");
    let environment_fields = ["profile", "packs", "corpora", "as_of", "jurisdiction"];
    assert_eq!(environment.len(), environment_fields.len());
    for field in environment_fields {
        assert!(
            environment.contains_key(field),
            "missing environment field `{field}`"
        );
    }
    assert_eq!(environment["profile"], "cn.default");
    assert_eq!(environment["packs"][0]["name"], "cn.constitution");
    assert_eq!(environment["packs"][0]["version"], "0.4.0");
    assert_eq!(environment["packs"][0]["trust"], "official");
    assert_eq!(environment["corpora"][0]["law"], "cn.constitution");
    assert_eq!(environment["corpora"][0]["version"], "2018");
    assert!(environment["as_of"].is_null());
    assert!(environment["jurisdiction"].is_null());
    assert_eq!(value["nodes"][0]["kind"], "assumption");
    assert_eq!(value["nodes"][1]["kind"], "interpretation_application");
    assert_eq!(value["nodes"][2]["kind"], "rule_application");
    assert_eq!(value["nodes"][3]["kind"], "gap");
    assert_eq!(value["nodes"][1]["interpretation"], 0);
    assert_eq!(value["nodes"][1]["premise"], 0);
    assert_eq!(value["interpretations"][0]["id"], "防卫解释");
    assert_eq!(value["interpretations"][0]["direction"], "expand");
    assert_eq!(value["assumptions"][0]["identity"], "user_asserted");
    assert_eq!(value["assumptions"][0]["occurred_at"], "2025-03-01");
    assert_eq!(value["assumptions"][0]["occurred_in"], "CN");
    assert_eq!(value["nodes"][2]["applicability"]["verdict"], "unchecked");
    assert_eq!(
        value["nodes"][2]["applicability"]["reason"]["detail"]["kind"],
        "rule_has_no_scope"
    );
    assert_eq!(
        value["nodes"][2]["applicability"]["basis"]["scope"]["effective_from"],
        Value::Null
    );
    assert_eq!(
        value["nodes"][3]["candidates"][0]["applicability"]["verdict"],
        "unchecked"
    );
    assert_eq!(value["nodes"][2]["bindings"][0]["parameter"], "p");
    assert_eq!(
        value["assumptions"][0]["sources"][0]["locator"],
        "中华人民共和国刑法第二十条第一款"
    );
    assert_eq!(value["assumptions"][0]["sources"][0]["quote"], "条文原文");
    assert_eq!(
        value["assumptions"][0]["sources"][0]["url"],
        "https://example.test/law?article=20"
    );
    assert_eq!(value["assumptions"][0]["sources"][0]["jurisdiction"], "CN");
    assert_eq!(
        value["assumptions"][0]["sources"][0]["retrieved_at"],
        "2026-11-21"
    );
    assert_eq!(value["assumptions"][0]["sources"][0]["hash"], "sha256:abc");
    assert_eq!(value["conflicts"][0]["left_by"]["kind"], "rules");
    assert_eq!(value["conflicts"][0]["resolution"]["kind"], "defeated");
    assert_eq!(value["conflicts"][0]["resolution"]["winner"], "left");
    assert_eq!(
        value["conflicts"][0]["resolution"]["basis"]["kind"],
        "priority"
    );
    let edge = &value["conflicts"][0]["resolution"]["basis"]["edges"][0];
    assert_eq!(edge["winner"], "正当防卫");
    assert_eq!(edge["loser"], "应负刑事责任规则");
    assert_eq!(edge["origin"]["kind"], "priority_declaration");
    assert_eq!(edge["origin"]["declared_in"], "cn.constitution");
    assert_eq!(edge["origin"]["sources"][0]["text"], "中华人民共和国立法法");
    assert_eq!(edge["origin"]["sources"][0]["locator"], "第九十二条");
    assert_eq!(edge["origin"]["sources"][0]["version"], "2020年修正");
    assert_eq!(
        value["open_obligations"][0]["kind"],
        "needs_human_determination"
    );
}

#[test]
fn a_v3_certificate_is_rejected_before_its_missing_resolution_basis() {
    // `certificate_v3.json` predates the resolution basis: its defeated
    // conflict carries only a winner. The version probe must reject it on the
    // version, not report a missing `basis` field the old writer never had.
    let error = Certificate::from_json(V3_SNAPSHOT).unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("unsupported certificate format version 3"),
        "{message}"
    );
    assert!(message.contains("this build supports 9"), "{message}");
    assert!(!message.contains("missing field"), "{message}");
}

#[test]
fn a_v4_certificate_is_rejected_before_its_missing_assumption_identity() {
    // `certificate_v4.json` predates the assumption identity. The version
    // probe must reject it on the version, not report a missing `identity`
    // field the old writer never had.
    let error = Certificate::from_json(V4_SNAPSHOT).unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("unsupported certificate format version 4"),
        "{message}"
    );
    assert!(message.contains("this build supports 9"), "{message}");
    assert!(!message.contains("missing field"), "{message}");
}

#[test]
fn a_v6_certificate_is_rejected_before_its_missing_applicability() {
    // `certificate_v6.json` predates the applicability record and the
    // assumption occurrences. The version probe must reject it on the version,
    // not report a missing field the old writer never had.
    let error = Certificate::from_json(V6_SNAPSHOT).unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("unsupported certificate format version 6"),
        "{message}"
    );
    assert!(message.contains("this build supports 9"), "{message}");
    assert!(!message.contains("missing field"), "{message}");
    assert!(!message.contains("applicability"), "{message}");
    assert!(!message.contains("occurred_at"), "{message}");
}

#[test]
fn a_v7_certificate_is_rejected_before_its_missing_axiom_instances() {
    // Version 7 predates universal elimination: it cannot express an
    // `axiom_instance` node or the `axiom_candidates` of a gap. The version
    // probe must reject it on the version, not read a current document as if
    // the older writer had said nothing about instantiation.
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["format_version"] = Value::from(7);
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("unsupported certificate format version 7"),
        "{message}"
    );
    assert!(message.contains("this build supports 9"), "{message}");
    assert!(!message.contains("missing field"), "{message}");
}

#[test]
fn a_v8_certificate_is_rejected_before_its_missing_witness_table() {
    // Version 8 predates the independent-witness table: it cannot express that
    // a conclusion has several derivations. The version probe must reject it
    // on the version, not report the missing `alternatives` field.
    let error = Certificate::from_json(V8_SNAPSHOT).unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("unsupported certificate format version 8"),
        "{message}"
    );
    assert!(message.contains("this build supports 9"), "{message}");
    assert!(!message.contains("missing field"), "{message}");
}

#[test]
fn a_v5_certificate_is_rejected_before_its_missing_interpretations() {
    // `certificate_v5.json` predates the interpretation table. The version
    // probe must reject it on the version, not report the missing field the
    // old writer could not have written.
    let error = Certificate::from_json(V5_SNAPSHOT).unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("unsupported certificate format version 5"),
        "{message}"
    );
    assert!(message.contains("this build supports 9"), "{message}");
    assert!(!message.contains("missing field"), "{message}");
    assert!(!message.contains("interpretations"), "{message}");
}

#[test]
fn a_true_v1_certificate_is_rejected_with_a_version_error() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    strip_new_source_fields(&mut value);
    value["format_version"] = Value::from(1);
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("unsupported certificate format version 1"),
        "{message}"
    );
    assert!(message.contains("supports 9"), "{message}");
}

#[test]
fn a_v2_certificate_is_rejected_before_its_missing_environment() {
    // `certificate_v2.json` predates the mandatory environment object. The
    // version probe must reject it on the version, not report a missing field
    // the old writer could not have written.
    let error = Certificate::from_json(V2_SNAPSHOT).unwrap_err();
    let message = error.to_string();
    assert!(
        message.contains("unsupported certificate format version 2"),
        "{message}"
    );
    assert!(message.contains("this build supports 9"), "{message}");
    assert!(!message.contains("missing field"), "{message}");
}

#[test]
fn source_fields_added_in_v2_still_use_defaults() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    strip_new_source_fields(&mut value);
    assert_eq!(value["format_version"], 9);
    let certificate = Certificate::from_json(&value.to_string())
        .expect("source fields added with #[serde(default)] may be omitted");
    let source = &certificate.assumptions[0].sources[0];
    assert!(source.quote.is_empty());
    assert!(source.url.is_empty());
    assert!(source.jurisdiction.is_empty());
    assert!(source.retrieved_at.is_empty());
    assert!(source.hash.is_empty());
}

#[test]
fn a_missing_environment_is_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value
        .as_object_mut()
        .unwrap()
        .remove("environment")
        .expect("fixture has an environment");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("missing field `environment`"),
        "{error}"
    );
}

#[test]
fn a_missing_environment_field_is_rejected_without_being_read_as_null() {
    for field in ["profile", "packs", "corpora", "as_of", "jurisdiction"] {
        let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
        value["environment"]
            .as_object_mut()
            .unwrap()
            .remove(field)
            .unwrap_or_else(|| panic!("fixture has environment.{field}"));
        let error = Certificate::from_json(&value.to_string()).unwrap_err();
        let message = error.to_string();
        assert!(
            message.contains(&format!("missing field `{field}`")),
            "{message}"
        );
    }
}

#[test]
fn an_explicit_null_profile_as_of_and_jurisdiction_are_accepted() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["environment"]["profile"] = Value::Null;
    value["environment"]["as_of"] = Value::Null;
    value["environment"]["jurisdiction"] = Value::Null;
    let certificate =
        Certificate::from_json(&value.to_string()).expect("explicit nulls are part of the format");
    let EnvironmentIdentity::Recorded(environment) = &certificate.environment else {
        panic!("a parsed certificate always records an environment");
    };
    assert!(environment.profile.is_none());
    assert!(environment.as_of.is_none());
    assert!(environment.jurisdiction.is_none());
}

#[test]
fn environment_dates_and_jurisdiction_strings_are_accepted_and_validated() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["environment"]["as_of"] = Value::from("2026-11-21");
    value["environment"]["jurisdiction"] = Value::from("CN");
    Certificate::from_json(&value.to_string()).expect("a real date and a code are valid");

    value["environment"]["as_of"] = Value::from("2026-02-30");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(error.to_string().contains("as_of"), "{error}");

    value["environment"]["as_of"] = Value::Null;
    value["environment"]["jurisdiction"] = Value::from("CN!");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(error.to_string().contains("jurisdiction"), "{error}");
}

#[test]
fn an_unknown_environment_field_or_trust_level_is_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["environment"]["future_field"] = Value::Bool(true);
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("unknown field `future_field`"),
        "{error}"
    );

    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["environment"]["packs"][0]["trust"] = Value::from("trusted");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(error.to_string().contains("trust"), "{error}");
}

#[test]
fn malformed_environment_hashes_and_duplicates_are_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["environment"]["packs"][0]["hash"] = Value::from("sha256:ABC");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(error.to_string().contains("hash"), "{error}");

    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["environment"]["corpora"][0]["file_sha256"] = Value::from("ABC");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(error.to_string().contains("file_sha256"), "{error}");

    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    let packs = value["environment"]["packs"].as_array().unwrap();
    let first = packs[0].clone();
    value["environment"]["packs"]
        .as_array_mut()
        .unwrap()
        .push(first);
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(error.to_string().contains("duplicated"), "{error}");
}

#[test]
fn an_unrecorded_environment_cannot_be_serialized() {
    let mut certificate = sample_certificate();
    certificate.environment = EnvironmentIdentity::Unrecorded;
    let error = certificate.to_json().unwrap_err();
    assert!(
        error.to_string().contains("not recorded"),
        "the serialization error must say why: {error}"
    );
    let error = certificate.to_json_pretty().unwrap_err();
    assert!(error.to_string().contains("not recorded"), "{error}");
}

#[test]
fn an_environment_identity_only_deserializes_from_an_object() {
    for text in ["null", "\"profile\"", "[]", "true"] {
        let error = serde_json::from_str::<EnvironmentIdentity>(text)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("EnvironmentRecord") || error.contains("environment"),
            "{text}: {error}"
        );
    }
    let empty = serde_json::from_str::<EnvironmentIdentity>(
        r#"{"profile":null,"packs":[],"corpora":[],"as_of":null,"jurisdiction":null}"#,
    )
    .expect("an object is the only accepted form");
    assert_eq!(empty, EnvironmentIdentity::none());
}

#[test]
fn every_source_field_survives_a_json_round_trip() {
    let certificate = sample_certificate();
    let json = certificate.to_json_pretty().unwrap();
    let decoded = Certificate::from_json(&json).unwrap();
    let source = &decoded.assumptions[0].sources[0];
    assert_eq!(source.text, "为了使国家、公共利益、本人或者他人的人身、财产和其他权利免受正在进行的不法侵害，而采取的制止不法侵害的行为，对不法侵害人造成损害的，属于正当防卫，不负刑事责任。");
    assert_eq!(source.locator, "中华人民共和国刑法第二十条第一款");
    assert_eq!(source.version, "2020年修正");
    assert_eq!(source.effective.as_deref(), Some("2021-03-01"));
    assert_eq!(source.note, "按现行条文形式化");
    assert_eq!(source.quote, "条文原文");
    assert_eq!(source.url, "https://example.test/law?article=20");
    assert_eq!(source.jurisdiction, "CN");
    assert_eq!(source.retrieved_at, "2026-11-21");
    assert_eq!(source.hash, "sha256:abc");
}

#[test]
fn unknown_format_version_is_rejected() {
    let text = SNAPSHOT.replace("\"format_version\": 9", "\"format_version\": 999");
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
    } = &certificate.nodes[2]
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

/// A conflict whose resolution round-trips through JSON, with both sides as
/// rules unless the resolution says otherwise.
fn conflict_with(resolution: Resolution) -> Conflict {
    Conflict {
        left: app(constant("结论甲"), constant("张三")),
        right: app(constant("结论乙"), constant("张三")),
        left_by: Provenance::Rules {
            rules: vec!["规则甲".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["规则乙".to_owned()],
        },
        resolution,
    }
}

fn declaration_edge(winner: &str, loser: &str) -> PriorityEdge {
    PriorityEdge {
        winner: winner.to_owned(),
        loser: loser.to_owned(),
        origin: PriorityOrigin::PriorityDeclaration {
            declared_in: "cn.order".to_owned(),
            sources: vec![source("中华人民共和国立法法", "第九十二条")],
        },
    }
}

#[test]
fn every_resolution_variant_round_trips() {
    let mut certificate = sample_certificate();
    certificate.conflicts = vec![
        conflict_with(Resolution::Defeated {
            winner: Side::Left,
            basis: ResolutionBasis::Assumption,
        }),
        conflict_with(Resolution::Defeated {
            winner: Side::Right,
            basis: ResolutionBasis::Priority {
                edges: vec![declaration_edge("规则乙", "规则甲")],
            },
        }),
        conflict_with(Resolution::Defeated {
            winner: Side::Left,
            basis: ResolutionBasis::Priority {
                edges: vec![
                    PriorityEdge {
                        winner: "规则甲".to_owned(),
                        loser: "规则乙".to_owned(),
                        origin: PriorityOrigin::RuleClause {
                            declaring_rule: "规则甲".to_owned(),
                            clause: PriorityClause::Prefer,
                            rule_sources: vec![source("规则甲法", "第一条")],
                        },
                    },
                    PriorityEdge {
                        winner: "规则甲".to_owned(),
                        loser: "规则乙".to_owned(),
                        origin: PriorityOrigin::RuleClause {
                            declaring_rule: "规则乙".to_owned(),
                            clause: PriorityClause::DefeatedBy,
                            rule_sources: vec![source("规则乙法", "第二条")],
                        },
                    },
                ],
            },
        }),
        conflict_with(Resolution::Unresolved {
            reason: UnresolvedReason::ConflictingAssumptions,
        }),
        conflict_with(Resolution::Unresolved {
            reason: UnresolvedReason::UnknownWitnesses,
        }),
        conflict_with(Resolution::Unresolved {
            reason: UnresolvedReason::NoPriority,
        }),
        conflict_with(Resolution::Unresolved {
            reason: UnresolvedReason::PriorityUnusable {
                declared: vec![
                    declaration_edge("规则甲", "规则乙"),
                    declaration_edge("规则乙", "规则甲"),
                ],
            },
        }),
    ];

    let json = certificate.to_json_pretty().unwrap();
    let decoded = Certificate::from_json(&json).expect("every variant round-trips");
    assert_eq!(decoded, certificate);
    assert_eq!(decoded.to_json_pretty().unwrap(), json);

    let value: Value = serde_json::from_str(&json).unwrap();
    assert_eq!(
        value["conflicts"][0]["resolution"]["basis"]["kind"],
        "assumption"
    );
    assert_eq!(
        value["conflicts"][2]["resolution"]["basis"]["edges"][0]["origin"]["clause"],
        "prefer"
    );
    assert_eq!(
        value["conflicts"][2]["resolution"]["basis"]["edges"][1]["origin"]["clause"],
        "defeated_by"
    );
    assert_eq!(
        value["conflicts"][3]["resolution"]["reason"]["kind"],
        "conflicting_assumptions"
    );
    assert_eq!(
        value["conflicts"][4]["resolution"]["reason"]["kind"],
        "unknown_witnesses"
    );
    assert_eq!(
        value["conflicts"][5]["resolution"]["reason"]["kind"],
        "no_priority"
    );
    assert_eq!(
        value["conflicts"][6]["resolution"]["reason"]["kind"],
        "priority_unusable"
    );
}

#[test]
fn every_fact_identity_round_trips() {
    let identities = [
        FactIdentity::Verified,
        FactIdentity::UserAsserted,
        FactIdentity::Assumed,
        FactIdentity::Disputed,
        FactIdentity::Stipulated,
    ];
    let mut certificate = sample_certificate();
    certificate.assumptions = identities
        .iter()
        .enumerate()
        .map(|(index, identity)| Assumption {
            proposition: constant(&format!("命题{index}")),
            identity: *identity,
            sources: Vec::new(),
            label: None,
            occurred_at: Explicit::none(),
            occurred_in: Explicit::none(),
        })
        .collect();

    let json = certificate.to_json_pretty().unwrap();
    let decoded = Certificate::from_json(&json).expect("every identity round-trips");
    assert_eq!(decoded, certificate);
    assert_eq!(
        decoded
            .assumptions
            .iter()
            .map(|assumption| assumption.identity)
            .collect::<Vec<_>>(),
        identities.to_vec()
    );

    let value: Value = serde_json::from_str(&json).unwrap();
    let encoded: Vec<&str> = value["assumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|assumption| assumption["identity"].as_str().unwrap())
        .collect();
    assert_eq!(
        encoded,
        [
            "verified",
            "user_asserted",
            "assumed",
            "disputed",
            "stipulated"
        ]
    );
}

#[test]
fn a_missing_assumption_identity_is_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["assumptions"][0]
        .as_object_mut()
        .unwrap()
        .remove("identity")
        .expect("the fixture records an identity");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("missing field `identity`"),
        "{error}"
    );
}

#[test]
fn an_unknown_fact_identity_is_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["assumptions"][0]["identity"] = Value::from("hearsay");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("unknown variant `hearsay`"),
        "{error}"
    );
}

#[test]
fn a_non_strict_fact_reason_round_trips() {
    for (identity, encoded) in [
        (FactIdentity::UserAsserted, "user_asserted"),
        (FactIdentity::Assumed, "assumed"),
    ] {
        let mut certificate = sample_certificate();
        certificate.conflicts = vec![conflict_with(Resolution::Unresolved {
            reason: UnresolvedReason::NonStrictFact { identity },
        })];

        let json = certificate.to_json_pretty().unwrap();
        let decoded = Certificate::from_json(&json).expect("the reason round-trips");
        assert_eq!(decoded, certificate);
        let value: Value = serde_json::from_str(&json).unwrap();
        assert_eq!(
            value["conflicts"][0]["resolution"]["reason"]["kind"],
            "non_strict_fact"
        );
        assert_eq!(
            value["conflicts"][0]["resolution"]["reason"]["identity"],
            encoded
        );
    }
}

#[test]
fn a_defeat_without_a_basis_is_rejected() {
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["conflicts"][0]["resolution"]
        .as_object_mut()
        .unwrap()
        .remove("basis");
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("missing field `basis`"),
        "{error}"
    );
}

#[test]
fn unknown_fields_inside_a_resolution_are_rejected() {
    for path in [
        &["conflicts", "0", "resolution", "future"][..],
        &["conflicts", "0", "resolution", "basis", "future"][..],
        &[
            "conflicts",
            "0",
            "resolution",
            "basis",
            "edges",
            "0",
            "future",
        ][..],
        &[
            "conflicts",
            "0",
            "resolution",
            "basis",
            "edges",
            "0",
            "origin",
            "future",
        ][..],
    ] {
        let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
        let mut cursor = &mut value;
        for (index, part) in path.iter().enumerate() {
            if index + 1 == path.len() {
                cursor[part] = Value::Bool(true);
            } else if let Ok(position) = part.parse::<usize>() {
                cursor = &mut cursor[position];
            } else {
                cursor = &mut cursor[*part];
            }
        }
        let error = Certificate::from_json(&value.to_string()).unwrap_err();
        assert!(
            error.to_string().contains("unknown field `future`"),
            "{path:?}: {error}"
        );
    }
}

#[test]
fn unknown_resolution_kinds_are_rejected() {
    // Resolution, basis, reason and origin are tagged unions; a tag this build
    // does not know is an error, not the closest variant.
    for (selector, replacement) in [
        (
            &["conflicts", "0", "resolution"][..],
            serde_json::json!({"kind": "settled"}),
        ),
        (
            &["conflicts", "0", "resolution", "basis"][..],
            serde_json::json!({"kind": "tradition", "edges": []}),
        ),
        (
            &[
                "conflicts",
                "0",
                "resolution",
                "basis",
                "edges",
                "0",
                "origin",
            ][..],
            serde_json::json!({"kind": "custom"}),
        ),
    ] {
        let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
        let mut cursor = &mut value;
        for (index, part) in selector.iter().enumerate() {
            if index + 1 == selector.len() {
                cursor[part] = replacement.clone();
            } else if let Ok(position) = part.parse::<usize>() {
                cursor = &mut cursor[position];
            } else {
                cursor = &mut cursor[*part];
            }
        }
        let error = Certificate::from_json(&value.to_string()).unwrap_err();
        assert!(
            error.to_string().contains("unknown variant"),
            "{selector:?}: {error}"
        );
    }

    // An unresolved reason is a tagged union as well.
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["conflicts"][0]["resolution"] = serde_json::json!({
        "kind": "unresolved",
        "reason": {"kind": "because"},
    });
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("unknown variant `because`"),
        "{error}"
    );

    // And a rule-internal clause is a plain enum value.
    let mut value: Value = serde_json::from_str(SNAPSHOT).unwrap();
    value["conflicts"][0]["resolution"]["basis"]["edges"][0]["origin"] = serde_json::json!({
        "kind": "rule_clause",
        "declaring_rule": "正当防卫",
        "clause": "overruled",
        "rule_sources": [],
    });
    let error = Certificate::from_json(&value.to_string()).unwrap_err();
    assert!(
        error.to_string().contains("unknown variant `overruled`"),
        "{error}"
    );
}
