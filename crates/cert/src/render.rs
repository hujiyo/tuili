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
//! spaces. A universal elimination is printed as
//! `▸ <conclusion>  〈公理 <declaration>〔<identity>〕〉`, followed by its first
//! source and the binding variables. A gap is printed as
//! `? <proposition>  【未闭合】` with its candidates, the universal facts that
//! could instantiate it (with their bindings and refusal reasons), missing
//! premises and blocking conditions.
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

use std::collections::{BTreeMap, BTreeSet};

use std_deduce_kernel::env::escape_control;
use std_deduce_kernel::pretty::{print_expr, print_parenthesized};
use std_deduce_kernel::Expr;

use crate::model::{Certificate, Node, NodeId};

/// Render a certificate as an indented derivation tree.
///
/// The output is the tree the certificate records. An invalid node reference
/// or a cyclic node graph is an error naming the offending node.
pub fn render(certificate: &Certificate) -> Result<String, String> {
    render_with_annotations(certificate, &BTreeMap::new())
}

/// Render a certificate, adding one per-node annotation to each rule
/// application line.
///
/// The certificate format records no applicability verdict, so a caller that
/// knows the derivation's verdicts can pass them by node id: the annotation is
/// printed after `⟨rule⟩` on that step's conclusion line (e.g.
/// `〔适用性未判定（…）〕`). The annotation is escaped like every other
/// external value. A node without an annotation prints exactly as [`render`]
/// does.
pub fn render_with_annotations(
    certificate: &Certificate,
    annotations: &BTreeMap<NodeId, String>,
) -> Result<String, String> {
    validate(certificate)?;

    let mut out = String::new();
    if let Some(root) = certificate.root {
        render_node(certificate, root, 0, annotations, &mut out)?;
        return Ok(out);
    }

    // No root: print every node not used as a premise elsewhere, then every
    // gap, in node order.
    let roots = root_nodes(certificate);
    for (index, id) in roots.into_iter().enumerate() {
        if index > 0 {
            out.push('\n');
        }
        render_node(certificate, id, 0, annotations, &mut out)?;
    }
    Ok(out)
}

/// The nodes printed when a certificate has no root: every assumption or rule
/// application that is not a premise of a rule step, then every gap, in node
/// order.
pub(crate) fn root_nodes(certificate: &Certificate) -> Vec<NodeId> {
    let mut used = BTreeSet::new();
    for node in &certificate.nodes {
        match node {
            Node::RuleApplication { premises, .. } => {
                used.extend(premises.iter().copied());
            }
            Node::InterpretationApplication { premise, .. } => {
                used.insert(*premise);
            }
            Node::Assumption { .. } | Node::AxiomInstance { .. } | Node::Gap { .. } => {}
        }
    }
    let mut roots = Vec::new();
    for (id, node) in certificate.nodes.iter().enumerate() {
        match node {
            Node::Assumption { .. }
            | Node::RuleApplication { .. }
            | Node::InterpretationApplication { .. }
            | Node::AxiomInstance { .. } => {
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
            Node::InterpretationApplication {
                interpretation,
                premise,
                ..
            } => {
                if *interpretation >= certificate.interpretations.len() {
                    return Err(format!(
                        "节点 {id}：引用了不存在的解释 {interpretation}：证书只有 {} 条解释",
                        certificate.interpretations.len()
                    ));
                }
                if *premise >= certificate.nodes.len() {
                    return Err(format!(
                        "节点 {id}：前提 {premise} 越界：证书只有 {} 个节点",
                        certificate.nodes.len()
                    ));
                }
            }
            Node::AxiomInstance { .. } | Node::Gap { .. } => {}
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
        match &certificate.nodes[id] {
            Node::RuleApplication { premises, .. } => {
                for premise in premises {
                    visit(certificate, *premise, state, path)?;
                }
            }
            Node::InterpretationApplication { premise, .. } => {
                visit(certificate, *premise, state, path)?;
            }
            Node::Assumption { .. } | Node::AxiomInstance { .. } | Node::Gap { .. } => {}
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
    annotations: &BTreeMap<NodeId, String>,
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
            computed,
            premises,
            bindings,
            guards,
            sources,
            ..
        } => {
            out.push_str(&format!(
                "{pad}▸ {}  ⟨{}⟩",
                print_expr(&Expr::from(conclusion)),
                escape_control(rule)
            ));
            if let Some(annotation) = annotations.get(&id) {
                out.push_str(&format!("〔{}〕", escape_control(annotation)));
            }
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
            // The arithmetic step, when the certificate records it: the
            // instance exactly as the rule wrote it, and the value the kernel
            // computed from it. A step without arithmetic prints nothing extra.
            if let Some(computed) = computed {
                out.push_str(&format!(
                    "{pad}  计算：{} = {}\n",
                    print_expr(&Expr::from(computed)),
                    print_expr(&Expr::from(conclusion))
                ));
            }
            // Guard judgements, one per declared guard: the substituted
            // comparison and its truth value. They are printed only when the
            // rule carries guards, so the form tree of an unguarded rule is
            // byte-for-byte the same as before.
            for guard in guards {
                out.push_str(&format!(
                    "{pad}  守卫：`{}` = {}\n",
                    print_parenthesized(&Expr::from(&guard.instance)),
                    guard_value_text(guard)
                ));
            }
            for premise in premises {
                render_node(certificate, *premise, depth + 1, annotations, out)?;
            }
        }
        Node::AxiomInstance {
            axiom,
            identity,
            bindings,
            conclusion,
            sources,
        } => {
            out.push_str(&format!(
                "{pad}▸ {}  〈公理 {}〔{}〕〉",
                print_expr(&Expr::from(conclusion)),
                escape_control(axiom),
                identity.label_zh()
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
        }
        Node::InterpretationApplication {
            interpretation,
            premise,
            conclusion,
        } => {
            let Some(entry) = certificate.interpretations.get(*interpretation) else {
                return Err(format!(
                    "节点 {id}：引用了不存在的解释 {interpretation}：证书只有 {} 条解释",
                    certificate.interpretations.len()
                ));
            };
            out.push_str(&format!(
                "{pad}▸ {}  〈解释 {}（{}）〉",
                print_expr(&Expr::from(conclusion)),
                escape_control(&entry.id),
                entry.direction.keyword()
            ));
            if let Some(source) = entry.sources.first() {
                out.push_str(&format!(" ← {}", source.one_line()));
            }
            out.push('\n');
            if let Some(source) = entry.sources.first() {
                if !source.note.is_empty() {
                    out.push_str(&format!("{pad}  注：{}\n", escape_control(&source.note)));
                }
            }
            render_node(certificate, *premise, depth + 1, annotations, out)?;
        }
        Node::Gap {
            proposition,
            candidates,
            axiom_candidates,
            note,
        } => {
            out.push_str(&format!(
                "{pad}? {}  【未闭合】\n",
                print_expr(&Expr::from(proposition))
            ));
            if let Some(note) = note {
                out.push_str(&format!("{pad}  {}\n", escape_control(note)));
            }
            for candidate in axiom_candidates {
                out.push_str(&format!(
                    "{pad}  公理候选 ⟨{}⟩",
                    escape_control(&candidate.axiom)
                ));
                if !candidate.bindings.is_empty() {
                    let bindings = candidate
                        .bindings
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
                    out.push_str(&format!("（绑定：{bindings}）"));
                }
                out.push('\n');
                match &candidate.problem {
                    Some(problem) => {
                        out.push_str(&format!("{pad}    未实例化：{}\n", escape_control(problem)))
                    }
                    None => out.push_str(&format!(
                        "{pad}    可由该公理实例化，但本次推导没有触发它\n"
                    )),
                }
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
                    // Disjunctive gaps carry one label per written branch:
                    // label each branch so a reader does not mistake the
                    // branches for independent missing premises. A certificate
                    // without labels (plain/existential gaps, or a hand-written
                    // certificate omitting them) keeps the flat wording.
                    if !candidate.missing_branches.is_empty() {
                        let missing = candidate
                            .missing
                            .iter()
                            .zip(candidate.missing_branches.iter())
                            .map(|(proposition, branch)| match branch {
                                Some(branch) => format!(
                                    "第 {} 个分支 {}",
                                    branch + 1,
                                    print_expr(&Expr::from(proposition))
                                ),
                                None => print_expr(&Expr::from(proposition)),
                            })
                            .collect::<Vec<_>>()
                            .join("；");
                        out.push_str(&format!("{pad}    缺：{missing}\n"));
                    } else {
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
                // Guards that did not let the candidate fire are the reason it
                // is listed at all: print the substituted comparison and
                // whether it was false or could not be decided. A guard that
                // held is not repeated here — it is not what is missing.
                for guard in &candidate.guards {
                    match guard.holds.as_ref() {
                        Some(true) => {}
                        Some(false) => out.push_str(&format!(
                            "{pad}    守卫：`{}` 不成立\n",
                            print_parenthesized(&Expr::from(&guard.instance))
                        )),
                        None => out.push_str(&format!(
                            "{pad}    守卫：`{}` 无法判定（守卫参数没有全部绑定，或操作数不是整数字面量）\n",
                            print_parenthesized(&Expr::from(&guard.instance))
                        )),
                    }
                }
            }
        }
    }
    Ok(())
}

/// The truth value of one guard record as the form tree prints it.
fn guard_value_text(guard: &crate::model::GuardRecord) -> &'static str {
    match guard.holds.as_ref() {
        Some(true) => "true",
        Some(false) => "false",
        None => "无法判定",
    }
}
