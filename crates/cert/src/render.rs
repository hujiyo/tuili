//! Human-readable rendering of a certificate.
//!
//! [`render`] prints the derivation tree a user sees from a [`Certificate`]
//! alone. It reads no reasoner state, so the printed tree describes exactly
//! the proof the certificate records.
//!
//! An assumption is printed as `· <proposition>  〔<identity>〕`, followed by
//! its label and its first source. A rule application is printed as
//! `▸ <conclusion>  ⟨<rule>⟩`, followed by its first source, that source's
//! note and the parameter bindings, then its premises indented by two more
//! spaces. A gap is printed as `? <proposition>  【未闭合】` with its
//! candidates, missing premises and blocking conditions.
//!
//! A certificate with no root prints, in node order, every assumption or rule
//! application that is not a premise of a rule step, and every gap, with one
//! blank line between roots.
//!
//! Rendering validates references and cycles only: an out-of-range root,
//! assumption or premise index, and a cycle in the node graph, are errors
//! naming the node rather than a panic or a placeholder. Whether a rule step
//! is a legal instance, and whether a gap is used as a premise, is
//! [`crate::check`]'s job, not this module's.

use std::collections::BTreeSet;

use std_deduce_kernel::env::escape_control;
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::Expr;

use crate::model::{Certificate, Node, NodeId};

/// Render a certificate as an indented derivation tree.
///
/// The output is the tree the certificate records. An invalid node reference
/// or a cyclic node graph is an error naming the offending node.
pub fn render(certificate: &Certificate) -> Result<String, String> {
    validate(certificate)?;

    let mut out = String::new();
    if let Some(root) = certificate.root {
        render_node(certificate, root, 0, &mut out)?;
        return Ok(out);
    }

    // No root: print every node not used as a premise elsewhere, then every
    // gap, in node order.
    let roots = root_nodes(certificate);
    for (index, id) in roots.into_iter().enumerate() {
        if index > 0 {
            out.push('\n');
        }
        render_node(certificate, id, 0, &mut out)?;
    }
    Ok(out)
}

/// The nodes printed when a certificate has no root: every assumption or rule
/// application that is not a premise of a rule step, then every gap, in node
/// order.
pub(crate) fn root_nodes(certificate: &Certificate) -> Vec<NodeId> {
    let mut used = BTreeSet::new();
    for node in &certificate.nodes {
        if let Node::RuleApplication { premises, .. } = node {
            used.extend(premises.iter().copied());
        }
    }
    let mut roots = Vec::new();
    for (id, node) in certificate.nodes.iter().enumerate() {
        match node {
            Node::Assumption { .. } | Node::RuleApplication { .. } => {
                if !used.contains(&id) {
                    roots.push(id);
                }
            }
            Node::Gap { .. } => roots.push(id),
        }
    }
    roots
}

/// Check every node reference and reject a cycle before anything is printed.
pub(crate) fn validate(certificate: &Certificate) -> Result<(), String> {
    if let Some(root) = certificate.root {
        if root >= certificate.nodes.len() {
            return Err(format!(
                "节点 {root}：根节点索引越界：证书只有 {} 个节点",
                certificate.nodes.len()
            ));
        }
    }
    for (id, node) in certificate.nodes.iter().enumerate() {
        match node {
            Node::Assumption { assumption } => {
                if *assumption >= certificate.assumptions.len() {
                    return Err(format!(
                        "节点 {id}：引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                        certificate.assumptions.len()
                    ));
                }
            }
            Node::RuleApplication { premises, .. } => {
                for premise in premises {
                    if *premise >= certificate.nodes.len() {
                        return Err(format!(
                            "节点 {id}：前提 {premise} 越界：证书只有 {} 个节点",
                            certificate.nodes.len()
                        ));
                    }
                }
            }
            Node::Gap { .. } => {}
        }
    }
    detect_cycle(certificate)
}

/// Reject a cycle in the premise graph of the whole certificate.
///
/// Rendering a cycle would recurse forever; the cycle is reported by the node
/// where it closes.
fn detect_cycle(certificate: &Certificate) -> Result<(), String> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum State {
        Unvisited,
        OnPath,
        Done,
    }

    fn visit(
        certificate: &Certificate,
        id: NodeId,
        state: &mut [State],
        path: &mut Vec<NodeId>,
    ) -> Result<(), String> {
        match state[id] {
            State::Done => return Ok(()),
            State::OnPath => {
                let start = path
                    .iter()
                    .position(|entry| *entry == id)
                    .ok_or_else(|| format!("节点 {id}：节点图成环，但无法重建环路径"))?;
                let mut cycle: Vec<String> = path[start..].iter().map(NodeId::to_string).collect();
                cycle.push(id.to_string());
                return Err(format!("节点 {id}：节点图成环：{}", cycle.join(" → ")));
            }
            State::Unvisited => {}
        }

        state[id] = State::OnPath;
        path.push(id);
        if let Node::RuleApplication { premises, .. } = &certificate.nodes[id] {
            for premise in premises {
                visit(certificate, *premise, state, path)?;
            }
        }
        path.pop();
        state[id] = State::Done;
        Ok(())
    }

    let mut state = vec![State::Unvisited; certificate.nodes.len()];
    let mut path = Vec::new();
    for id in 0..certificate.nodes.len() {
        visit(certificate, id, &mut state, &mut path)?;
    }
    Ok(())
}

fn render_node(
    certificate: &Certificate,
    id: NodeId,
    depth: usize,
    out: &mut String,
) -> Result<(), String> {
    let pad = "  ".repeat(depth);
    let Some(node) = certificate.nodes.get(id) else {
        return Err(format!(
            "节点 {id}：节点索引越界：证书只有 {} 个节点",
            certificate.nodes.len()
        ));
    };

    match node {
        Node::Assumption { assumption } => {
            let Some(entry) = certificate.assumptions.get(*assumption) else {
                return Err(format!(
                    "节点 {id}：引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                    certificate.assumptions.len()
                ));
            };
            out.push_str(&format!(
                "{pad}· {}  〔{}〕",
                print_expr(&Expr::from(&entry.proposition)),
                entry.identity.label_zh()
            ));
            if let Some(label) = &entry.label {
                out.push_str(&format!("  [{}]", escape_control(label)));
            }
            if let Some(source) = entry.sources.first() {
                out.push_str(&format!("  ← {}", source.one_line()));
            }
            out.push('\n');
        }
        Node::RuleApplication {
            rule,
            conclusion,
            premises,
            bindings,
            sources,
        } => {
            out.push_str(&format!(
                "{pad}▸ {}  ⟨{}⟩",
                print_expr(&Expr::from(conclusion)),
                escape_control(rule)
            ));
            if let Some(source) = sources.first() {
                out.push_str(&format!(" ← {}", source.one_line()));
            }
            out.push('\n');
            if let Some(source) = sources.first() {
                if !source.note.is_empty() {
                    out.push_str(&format!("{pad}  注：{}\n", escape_control(&source.note)));
                }
            }
            if !bindings.is_empty() {
                let instance = bindings
                    .iter()
                    .map(|binding| {
                        format!(
                            "{} ↦ {}",
                            escape_control(&binding.parameter),
                            print_expr(&Expr::from(&binding.value))
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("，");
                out.push_str(&format!("{pad}  实例：{instance}\n"));
            }
            for premise in premises {
                render_node(certificate, *premise, depth + 1, out)?;
            }
        }
        Node::Gap {
            proposition,
            candidates,
            note,
        } => {
            out.push_str(&format!(
                "{pad}? {}  【未闭合】\n",
                print_expr(&Expr::from(proposition))
            ));
            if let Some(note) = note {
                out.push_str(&format!("{pad}  {}\n", escape_control(note)));
            }
            for candidate in candidates {
                out.push_str(&format!(
                    "{pad}  候选 ⟨{}⟩",
                    escape_control(&candidate.rule)
                ));
                if let Some(source) = candidate.sources.first() {
                    out.push_str(&format!(" ← {}", source.one_line()));
                }
                out.push('\n');
                if !candidate.missing.is_empty() {
                    out.push_str(&format!(
                        "{pad}    缺：{}\n",
                        candidate
                            .missing
                            .iter()
                            .map(|proposition| print_expr(&Expr::from(proposition)))
                            .collect::<Vec<_>>()
                            .join("；")
                    ));
                }
                for blocked in &candidate.blocked_by {
                    // The certificate's assumption table is the only identity
                    // record available here. A blocker derived by a rule has
                    // none, and then the line keeps its original wording.
                    let identity = certificate
                        .assumptions
                        .iter()
                        .find(|entry| &entry.proposition == blocked)
                        .map(|entry| format!("〔{}〕", entry.identity.label_zh()))
                        .unwrap_or_default();
                    out.push_str(&format!(
                        "{pad}    被阻断：「{}」{}已成立\n",
                        print_expr(&Expr::from(blocked)),
                        identity
                    ));
                }
            }
        }
    }
    Ok(())
}
