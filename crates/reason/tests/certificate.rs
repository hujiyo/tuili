//! Conversion from reasoner derivations to certificates, checked by the
//! independent certificate layer.

use std::path::Path;

use std_deduce_cert as cert;
use std_deduce_kernel::Expr;
use std_deduce_lang::Library;
use std_deduce_reason::{certificate, Derivation, Node as ReasonNode, Reasoner};

fn example(name: &str) -> Library {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name);
    let src =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let mut lib = Library::new();
    lib.load(name, &src)
        .unwrap_or_else(|e| panic!("load {name}: {e}"));
    lib
}

/// The same shape the CLI builds: all derived facts, plus a gap node when the
/// goal is unreachable.
fn derive(lib: &Library, goal: &Expr) -> Derivation {
    let mut r = Reasoner::new(&lib.env);
    r.assume_ledger_axioms().unwrap();
    r.saturate().unwrap();
    let mut d = r.derivation();
    if r.knows(goal) {
        d.root = r.root_for(goal);
    } else {
        let ex = r.explain(goal);
        let id = d.nodes.len();
        d.nodes.push(ReasonNode::Gap {
            prop: goal.clone(),
            candidates: ex.candidates,
            note: ex.note,
        });
        d.root = Some(id);
    }
    d
}

fn constitution_goal() -> Expr {
    Expr::apps(
        Expr::constant("不受侵犯"),
        [Expr::constant("张三"), Expr::constant("甲宅")],
    )
}

#[test]
fn constitution_certificate_round_trips_and_checks() {
    let lib = example("constitution-39.std");
    let d = derive(&lib, &constitution_goal());
    assert!(d.root.is_some(), "the goal must be derived");

    let certificate = certificate(&d).expect("the derivation converts");
    let pretty = certificate.to_json_pretty().unwrap();
    let decoded = cert::Certificate::from_json(&pretty).expect("the JSON round-trips");
    assert_eq!(decoded, certificate);
    assert_eq!(decoded.to_json_pretty().unwrap(), pretty);

    let report = cert::check(&lib.env, &decoded).expect("the certificate checks");
    assert!(report.root_proved);
    assert_eq!(report.nodes_checked, certificate.nodes.len());
}

#[test]
fn gap_certificate_is_valid_but_the_root_is_not_proved() {
    let lib = example("刑法第二十条-基本.std");
    let goal = Expr::apps(Expr::constant("应当负刑事责任"), [Expr::constant("乙行为")]);
    let d = derive(&lib, &goal);
    let certificate = certificate(&d).expect("the gap derivation converts");

    let root = certificate.root.expect("a gap certificate has a root");
    let cert::Node::Gap {
        proposition,
        candidates,
        ..
    } = &certificate.nodes[root]
    else {
        panic!("the root of an unreachable goal must be a gap");
    };
    assert_eq!(
        proposition,
        &cert::CertExpr::try_from(&goal).unwrap(),
        "the gap keeps the queried proposition"
    );
    assert!(
        candidates
            .iter()
            .any(|c| c.rule == "防卫过当应负刑责" && !c.missing.is_empty()),
        "the candidate rule and its missing premise must survive conversion"
    );
    assert!(
        certificate.open_obligations.iter().any(|obligation| {
            obligation.kind == cert::ObligationKind::MissingPremise
                && obligation.nodes == vec![root]
        }),
        "a gap becomes a MissingPremise obligation: {:?}",
        certificate.open_obligations
    );

    let report = cert::check(&lib.env, &certificate).expect("a gap certificate is well-formed");
    assert!(!report.root_proved);
}

#[test]
fn conflicts_keep_both_sides_provenance_and_resolution() {
    let lib = example("法律位阶-河南种子案-裁决.std");
    let goal = Expr::apps(
        Expr::constant("应适用"),
        [Expr::constant("种子法"), Expr::constant("汝阳种子公司案")],
    );
    let d = derive(&lib, &goal);
    assert!(!d.conflicts.is_empty(), "the example records a conflict");

    let certificate = certificate(&d).expect("the derivation converts");
    assert_eq!(certificate.conflicts.len(), d.conflicts.len());

    let conflict = &certificate.conflicts[0];
    let cert::Resolution::Defeated { winner } = &conflict.resolution else {
        panic!("the example has an explicit priority, so the conflict is decided");
    };
    let winning = match winner {
        cert::Side::Left => &conflict.left,
        cert::Side::Right => &conflict.right,
    };
    assert_eq!(
        winning,
        &cert::CertExpr::try_from(&goal).unwrap(),
        "the winning side is the proposition the goal asked for"
    );
    assert!(matches!(conflict.left_by, cert::Provenance::Rules { .. }));
    assert!(matches!(conflict.right_by, cert::Provenance::Rules { .. }));
    assert!(
        !certificate
            .open_obligations
            .iter()
            .any(|obligation| obligation.kind == cert::ObligationKind::UnresolvedConflict),
        "a defeated conflict is decided, so it is not an open obligation"
    );

    let report = cert::check(&lib.env, &certificate).expect("the certificate checks");
    assert!(report.root_proved);
}

#[test]
fn an_unencodable_expression_is_a_clear_error() {
    if usize::BITS <= 32 {
        return;
    }
    let index = u32::MAX as usize + 1;
    let d = Derivation {
        nodes: vec![ReasonNode::Gap {
            prop: Expr::var(index),
            candidates: Vec::new(),
            note: None,
        }],
        root: Some(0),
        conflicts: Vec::new(),
    };
    let error = certificate(&d).expect_err("the index does not fit the certificate format");
    assert!(error.contains("节点 0"), "{error}");
    assert!(error.contains("缺口命题"), "{error}");
    assert!(error.contains("de Bruijn"), "{error}");
}
