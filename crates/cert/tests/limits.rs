//! Malformed and oversized certificate JSON.
//!
//! `Certificate::from_json` is the boundary where an untrusted file becomes a
//! certificate. Every case here must return an ordinary error: no panic, no
//! stack overflow, no unbounded allocation, and a message that says which limit
//! was hit or which field was wrong.

use serde_json::{json, Value};
use std_deduce_cert::{
    CertExpr, Certificate, EnvironmentIdentity, Metadata, Node, MAX_CERT_ASSUMPTIONS,
    MAX_CERT_EXPR_NODES, MAX_CERT_JSON_BYTES, MAX_CERT_NODES,
};
use std_deduce_kernel::env::Env;

const FIXTURE: &str = include_str!("fixtures/certificate_v5.json");

/// A recorded environment with no profile, packs, corpora or dates.
fn empty_environment() -> Value {
    serde_json::to_value(EnvironmentIdentity::none()).expect("an empty identity serializes")
}

/// A syntactically complete certificate around the given assumptions and nodes.
fn certificate_json(assumptions: Value, nodes: Value, root: Value) -> String {
    json!({
        "format_version": 5,
        "environment": empty_environment(),
        "assumptions": assumptions,
        "nodes": nodes,
        "root": root,
        "conflicts": [],
        "open_obligations": [],
        "metadata": {
            "generated_at": null,
            "tool": null,
            "tool_version": null
        }
    })
    .to_string()
}

fn gap_node() -> Value {
    json!({
        "kind": "gap",
        "proposition": { "kind": "const", "name": "命题" }
    })
}

fn self_asserted_assumption() -> Value {
    json!({
        "proposition": { "kind": "const", "name": "命题" },
        "identity": "user_asserted"
    })
}

/// Parse and require a rejection, formatting only the input's size rather than
/// dumping a successfully decoded certificate whose debug form is enormous.
fn rejected(text: &str, what: &str) -> String {
    match Certificate::from_json(text) {
        Ok(_) => panic!(
            "{what}: the certificate was accepted ({} bytes)",
            text.len()
        ),
        Err(error) => error.to_string(),
    }
}

/// A balanced application tree with `2 * leaves - 1` expression nodes and a
/// shallow JSON nesting depth, so a size limit can be reached without the
/// deserializer's recursion limit firing first.
fn application_tree(leaves: usize) -> Value {
    let mut level: Vec<Value> = (0..leaves)
        .map(|_| json!({ "kind": "const", "name": "c" }))
        .collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut iter = level.into_iter();
        while let Some(left) = iter.next() {
            match iter.next() {
                Some(right) => next.push(json!({
                    "kind": "app",
                    "func": left,
                    "arg": right
                })),
                None => next.push(left),
            }
        }
        level = next;
    }
    level.pop().expect("at least one leaf")
}

#[test]
fn the_reference_certificate_still_parses() {
    Certificate::from_json(FIXTURE).expect("the v5 fixture must remain valid");
}

#[test]
fn a_missing_field_is_rejected_by_name() {
    let mut value: Value = serde_json::from_str(FIXTURE).expect("fixture is JSON");
    value
        .as_object_mut()
        .expect("certificate is an object")
        .remove("nodes");
    let error = rejected(&value.to_string(), "a certificate without nodes");
    assert!(
        error.contains("missing field `nodes`"),
        "the error must name the missing field, got: {error}"
    );
}

#[test]
fn a_wrongly_typed_field_is_rejected() {
    let mut value: Value = serde_json::from_str(FIXTURE).expect("fixture is JSON");
    value["nodes"] = json!(7);
    let error = rejected(&value.to_string(), "a node list that is a number");
    assert!(
        error.contains("invalid type"),
        "the error must describe the type mismatch, got: {error}"
    );
}

/// JSON has no `NaN` literal: it must fail as a syntax error with a position,
/// not be read as a number.
#[test]
fn a_nan_number_is_rejected() {
    let text = FIXTURE.replacen("\"format_version\": 5", "\"format_version\": NaN", 1);
    assert_ne!(text, FIXTURE, "the fixture must contain format_version");
    let error = rejected(&text, "NaN");
    assert!(
        error.contains("line ") && error.contains("column "),
        "a syntax error must carry a position, got: {error}"
    );
}

/// `serde_json`'s recursion limit is the depth bound for certificate
/// expressions. A 5000-deep application must be rejected while parsing, not
/// overflow the stack.
#[test]
fn a_deeply_nested_expression_is_rejected() {
    let depth = 5_000;
    let expression = format!(
        "{}{}{}",
        "{\"kind\":\"app\",\"func\":".repeat(depth),
        "{\"kind\":\"const\",\"name\":\"p\"}",
        ",\"arg\":{\"kind\":\"const\",\"name\":\"x\"}}".repeat(depth)
    );
    let text = format!(
        "{{\"format_version\":5,\"environment\":{},\"assumptions\":[],\
         \"nodes\":[{{\"kind\":\"gap\",\"proposition\":{expression}}}],\"root\":null,\
         \"conflicts\":[],\"open_obligations\":[],\"metadata\":{{}}}}",
        empty_environment()
    );
    let error = rejected(&text, "deep nesting");
    assert!(
        error.contains("recursion limit"),
        "the deserializer's recursion limit must reject it, got: {error}"
    );
}

#[test]
fn an_oversized_json_document_is_rejected_before_parsing() {
    let text = " ".repeat(MAX_CERT_JSON_BYTES + 1);
    let error = rejected(&text, "an oversized document");
    assert!(
        error.contains("字节上限"),
        "the error must name the byte limit, got: {error}"
    );
}

#[test]
fn a_certificate_at_the_node_limit_is_accepted() {
    let nodes: Vec<Value> = (0..MAX_CERT_NODES).map(|_| gap_node()).collect();
    let text = certificate_json(json!([]), json!(nodes), Value::Null);
    Certificate::from_json(&text).expect("exactly the node limit must still parse");
}

#[test]
fn a_certificate_over_the_node_limit_is_rejected() {
    let nodes: Vec<Value> = (0..MAX_CERT_NODES + 1).map(|_| gap_node()).collect();
    let text = certificate_json(json!([]), json!(nodes), Value::Null);
    let error = rejected(&text, "too many nodes");
    assert!(
        error.contains("节点数量超过上限"),
        "the error must name the node limit, got: {error}"
    );
}

#[test]
fn a_certificate_at_the_assumption_limit_is_accepted() {
    let assumptions: Vec<Value> = (0..MAX_CERT_ASSUMPTIONS)
        .map(|_| self_asserted_assumption())
        .collect();
    let text = certificate_json(json!(assumptions), json!([]), Value::Null);
    Certificate::from_json(&text).expect("exactly the assumption limit must still parse");
}

#[test]
fn a_certificate_over_the_assumption_limit_is_rejected() {
    let assumptions: Vec<Value> = (0..MAX_CERT_ASSUMPTIONS + 1)
        .map(|_| self_asserted_assumption())
        .collect();
    let text = certificate_json(json!(assumptions), json!([]), Value::Null);
    let error = rejected(&text, "too many assumptions");
    assert!(
        error.contains("假设数量超过上限"),
        "the error must name the assumption limit, got: {error}"
    );
}

#[test]
fn the_largest_expression_within_the_node_limit_is_accepted() {
    // A certificate expression is a binary tree, so its node count is always
    // odd: the largest count that fits under the bound is `2 * leaves - 1`
    // with `leaves = MAX / 2` leaves, i.e. one node below the bound.
    let expression = application_tree(MAX_CERT_EXPR_NODES / 2);
    let nodes = json!([{
        "kind": "gap",
        "proposition": expression
    }]);
    let text = certificate_json(json!([]), nodes, Value::Null);
    Certificate::from_json(&text)
        .expect("the largest odd expression under the limit must still parse");
}

#[test]
fn an_expression_over_the_node_limit_is_rejected() {
    let expression = application_tree(MAX_CERT_EXPR_NODES / 2 + 1);
    let nodes = json!([{
        "kind": "gap",
        "proposition": expression
    }]);
    let text = certificate_json(json!([]), nodes, Value::Null);
    let error = rejected(&text, "an oversized expression");
    assert!(
        error.contains("表达式"),
        "the error must identify the oversized expression, got: {error}"
    );
}

/// The size bounds hold on the way out as well: a certificate that
/// `from_json` would refuse must not be serialized into a file.
#[test]
fn an_oversized_certificate_is_not_serialized() {
    let certificate = Certificate {
        format_version: std_deduce_cert::FormatVersion::CURRENT,
        environment: EnvironmentIdentity::none(),
        assumptions: Vec::new(),
        nodes: vec![
            Node::Gap {
                proposition: CertExpr::Const {
                    name: "命题".to_owned()
                },
                candidates: Vec::new(),
                note: None,
            };
            MAX_CERT_NODES + 1
        ],
        root: None,
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Metadata::default(),
    };
    let error = certificate
        .to_json()
        .expect_err("oversized certificates must not serialize");
    assert!(
        error.to_string().contains("节点数量超过上限"),
        "the error must name the node limit, got: {error}"
    );
}

/// A certificate whose root index points past the node list parses (indices
/// are semantic), then the checker must reject it with a locatable error.
#[test]
fn a_root_index_past_the_node_list_is_rejected_by_the_checker() {
    let text = certificate_json(json!([]), json!([gap_node()]), json!(7));
    let certificate = Certificate::from_json(&text).expect("an out-of-range index is still JSON");
    let error = std_deduce_cert::check(&Env::new(), &certificate)
        .expect_err("the checker must reject an out-of-range root");
    assert!(
        error.to_string().contains("越界"),
        "the error must say the index is out of range, got: {error}"
    );
}
