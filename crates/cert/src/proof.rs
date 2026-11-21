//! Kernel proof terms built from a certificate's monotone skeleton.
//!
//! [`kernel_proof`] translates a [`Certificate`] into kernel terms and asks
//! the kernel to check every rule application:
//!
//! * every assumption is pushed into one [`Ctx`], in certificate order, so the
//!   node citing assumption `i` is `Var(assumptions.len() - 1 - i)`;
//! * a rule node becomes `Const(rule)` applied first to the parameter values
//!   from its bindings (in the rule's parameter order) and then to the proof
//!   terms of its premises (in the rule's premise order);
//! * a [`Node::Gap`] has no proof term and cannot be a premise. A gap may be
//!   the root; the report then has `root_proved = false`.
//!
//! The check is deliberately monotone: `unless` conditions are not part of the
//! kernel type of a rule and are not inspected here. A certificate whose
//! blocker is already proved still has a well-typed monotone proof term. The
//! side conditions are a separate layer; this function must not be read as
//! establishing the legal conclusion.
//!
//! Structural errors (unknown rules, missing or extra bindings, out-of-range
//! or forward premise references, gaps used as premises, bad assumption
//! indices) are reported with the node they belong to. The kernel remains the
//! authority on types: a step is successful only when `check` accepts its
//! term at the node's conclusion.

use std::collections::BTreeMap;
use std::fmt;

use std_deduce_kernel::env::DeclKind;
use std_deduce_kernel::term::is_closed;
use std_deduce_kernel::{check as kernel_check, Ctx, Env, Expr};

use crate::model::{Certificate, Node, NodeId};

/// A successful kernel check of a certificate's monotone skeleton.
#[derive(Debug, Clone, PartialEq)]
pub struct KernelProofReport {
    /// The kernel term for the root node. `None` when the certificate has no
    /// root or the root is a [`Node::Gap`].
    pub root_term: Option<Expr>,
    /// Whether the root was accepted by the kernel. False for a gap or a
    /// missing root; no proof is invented for either.
    pub root_proved: bool,
    /// Every rule application, in node order. A step whose check failed is
    /// returned as an error instead, so every entry here passed.
    pub steps: Vec<KernelStep>,
}

/// One rule application that passed the kernel check.
#[derive(Debug, Clone, PartialEq)]
pub struct KernelStep {
    /// The rule application node this term belongs to.
    pub node: NodeId,
    /// The rule constant the term is headed by.
    pub rule: String,
    /// `Const(rule)` applied to the parameter values and premise proofs.
    pub term: Expr,
    /// Whether the kernel accepted `term` at the node's conclusion. A
    /// rejection is returned as a [`KernelProofError`], so entries in a
    /// returned report are always `true`.
    pub checked: bool,
}

/// A certificate cannot be turned into a kernel-checked proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelProofError {
    /// The offending node, when the failure belongs to one.
    pub node: Option<NodeId>,
    /// The failed criterion, including the values involved.
    pub message: String,
}

impl KernelProofError {
    fn at(node: NodeId, message: impl Into<String>) -> Self {
        KernelProofError {
            node: Some(node),
            message: message.into(),
        }
    }
}

impl fmt::Display for KernelProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.node {
            Some(node) => write!(f, "节点 {node}：{}", self.message),
            None => f.write_str(&self.message),
        }
    }
}

impl std::error::Error for KernelProofError {}

/// Build the kernel proof term behind a certificate and check every step.
///
/// The assumptions form the local context; rule nodes are rebuilt from their
/// bindings and cited premises. A [`Node::Gap`] contributes no term. See the
/// module documentation for the translation and for what is deliberately out
/// of scope (`unless`).
pub fn kernel_proof(env: &Env, cert: &Certificate) -> Result<KernelProofReport, KernelProofError> {
    if let Some(root) = cert.root {
        if root >= cert.nodes.len() {
            return Err(KernelProofError::at(
                root,
                format!("根节点索引越界：证书只有 {} 个节点", cert.nodes.len()),
            ));
        }
    }

    // Every assumption is a hypothesis of the same derivation, so they share
    // one context in certificate order. Each hypothesis must itself be a
    // proposition: a context entry that is not a type would make the proof
    // meaningless even if the kernel never happened to inspect it.
    let mut ctx = Ctx::new();
    for (index, assumption) in cert.assumptions.iter().enumerate() {
        let proposition = Expr::from(&assumption.proposition);
        kernel_check::check(env, &Ctx::new(), &proposition, &Expr::Sort(0)).map_err(|error| {
            let node = cert.nodes.iter().position(
                |node| matches!(node, Node::Assumption { assumption } if *assumption == index),
            );
            KernelProofError {
                node,
                message: format!("假设 {index} 不是命题：{error}"),
            }
        })?;
        ctx.push(None, proposition);
    }

    let mut proofs: Vec<Option<Expr>> = vec![None; cert.nodes.len()];
    let mut steps = Vec::new();

    for (id, node) in cert.nodes.iter().enumerate() {
        match node {
            Node::Assumption { assumption } => {
                if *assumption >= cert.assumptions.len() {
                    return Err(KernelProofError::at(
                        id,
                        format!(
                            "引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                            cert.assumptions.len()
                        ),
                    ));
                }
                // The last assumption pushed is the innermost binder.
                let index = cert.assumptions.len() - 1 - *assumption;
                proofs[id] = Some(Expr::Var(index));
            }
            Node::RuleApplication {
                rule,
                conclusion,
                premises,
                bindings,
                ..
            } => {
                let decl = env
                    .get(rule)
                    .ok_or_else(|| KernelProofError::at(id, format!("未知规则 `{rule}`")))?;
                let DeclKind::Rule(rule_decl) = &decl.kind else {
                    return Err(KernelProofError::at(id, format!("`{rule}` 不是规则")));
                };

                if premises.len() != rule_decl.premises.len() {
                    return Err(KernelProofError::at(
                        id,
                        format!(
                            "规则 `{rule}` 有 {} 个前提，本步引用了 {} 个节点",
                            rule_decl.premises.len(),
                            premises.len()
                        ),
                    ));
                }

                let mut binding_map: BTreeMap<&str, Expr> = BTreeMap::new();
                for entry in bindings {
                    if !rule_decl
                        .params
                        .iter()
                        .any(|(parameter, _)| parameter.as_ref() == entry.parameter)
                    {
                        return Err(KernelProofError::at(
                            id,
                            format!("绑定参数 `{}` 不是规则 `{rule}` 的参数", entry.parameter),
                        ));
                    }
                    if binding_map.contains_key(entry.parameter.as_str()) {
                        return Err(KernelProofError::at(
                            id,
                            format!("参数 `{}` 被重复绑定", entry.parameter),
                        ));
                    }
                    let value = Expr::from(&entry.value);
                    if !is_closed(&value) {
                        return Err(KernelProofError::at(
                            id,
                            format!("参数 `{}` 的绑定值不是闭合项", entry.parameter),
                        ));
                    }
                    binding_map.insert(entry.parameter.as_str(), value);
                }

                let mut arguments =
                    Vec::with_capacity(rule_decl.params.len() + rule_decl.premises.len());
                for (parameter, _) in &rule_decl.params {
                    let value = binding_map.get(parameter.as_ref()).ok_or_else(|| {
                        KernelProofError::at(
                            id,
                            format!(
                                "参数 `{parameter}` 没有绑定；本步不是规则 `{rule}` 的完整实例"
                            ),
                        )
                    })?;
                    arguments.push(value.clone());
                }

                for premise in premises {
                    if *premise >= cert.nodes.len() {
                        return Err(KernelProofError::at(
                            id,
                            format!(
                                "前提节点索引 {premise} 越界：证书只有 {} 个节点",
                                cert.nodes.len()
                            ),
                        ));
                    }
                    if *premise >= id {
                        return Err(KernelProofError::at(
                            id,
                            format!("前提节点 {premise} 必须是当前节点之前的节点"),
                        ));
                    }
                    let proof = proofs[*premise].as_ref().ok_or_else(|| {
                        let reason = if matches!(&cert.nodes[*premise], Node::Gap { .. }) {
                            "是未闭合的缺口，不能充当前提"
                        } else {
                            "没有可用的证明项"
                        };
                        KernelProofError::at(id, format!("前提 {premise} {reason}"))
                    })?;
                    arguments.push(proof.clone());
                }

                let term = Expr::apps(Expr::constant(rule), arguments);
                let conclusion_expr = Expr::from(conclusion);
                // The claimed conclusion is a proposition in its own right,
                // not just a type that happens to match in the assumption
                // context. Otherwise an open expression could hide behind a
                // well-typed step.
                kernel_check::check(env, &Ctx::new(), &conclusion_expr, &Expr::Sort(0))
                    .map_err(|error| KernelProofError::at(id, format!("结论不是命题：{error}")))?;
                kernel_check::check(env, &ctx, &term, &conclusion_expr).map_err(|error| {
                    KernelProofError::at(
                        id,
                        format!("规则 `{rule}` 的证明项未通过内核检查：{error}"),
                    )
                })?;

                steps.push(KernelStep {
                    node: id,
                    rule: rule.clone(),
                    term: term.clone(),
                    checked: true,
                });
                proofs[id] = Some(term);
            }
            Node::Gap { .. } => {}
        }
    }

    let root_term = match cert.root {
        None => None,
        Some(root) => match &cert.nodes[root] {
            Node::Gap { .. } => None,
            Node::Assumption { assumption } => {
                let entry = cert.assumptions.get(*assumption).ok_or_else(|| {
                    KernelProofError::at(
                        root,
                        format!(
                            "引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                            cert.assumptions.len()
                        ),
                    )
                })?;
                let term = proofs[root]
                    .clone()
                    .ok_or_else(|| KernelProofError::at(root, "假设节点没有可用的证明项"))?;
                let proposition = Expr::from(&entry.proposition);
                kernel_check::check(env, &ctx, &term, &proposition).map_err(|error| {
                    KernelProofError::at(root, format!("根节点的假设证明项未通过内核检查：{error}"))
                })?;
                Some(term)
            }
            Node::RuleApplication { .. } => Some(
                proofs[root]
                    .clone()
                    .ok_or_else(|| KernelProofError::at(root, "规则节点没有可用的证明项"))?,
            ),
        },
    };

    Ok(KernelProofReport {
        root_proved: root_term.is_some(),
        root_term,
        steps,
    })
}
