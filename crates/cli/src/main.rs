//! Command-line interface.
//!
//! Commands are line-oriented:
//!
//! ```text
//! :load <file>            load a theory file
//! :inspect                dump the ledger
//! :why <term>             derive, print the certificate's tree, and check it
//! :gap <term>             explain what is missing for a goal
//! :cert <term>            derive and print the goal's certificate JSON
//! :check <file>           check a certificate JSON against the loaded environment
//! :given <term>           add an assumption by hand
//! :quit
//! ```
//!
//! `:why` prints the derivation tree rendered from the generated certificate,
//! then runs [`std_deduce_cert::check`] and [`std_deduce_cert::kernel_proof`]
//! on that same certificate. Its three outcomes are:
//!
//! * proved — the tree is printed, both layers accept the certificate, and
//!   the certificate leaves nothing open;
//! * a gap — the certificate is valid but its root is a gap, so the conclusion
//!   is not proved;
//! * a conflict — both derivations are printed and the process exits non-zero.
//!
//! A certificate that fails either layer is an error (exit `2`), never a
//! successful query. A conclusion caught in an unresolved conflict is kept out
//! of the fact base, but it is never dropped silently.
//!
//! `:cert` writes only the certificate JSON to stdout; a gap becomes a
//! `MissingPremise` obligation and an unresolved conflict becomes an
//! `UnresolvedConflict` obligation in that JSON.
//!
//! `:check` requires a loaded theory and runs two layers in order:
//!
//! 1. [`std_deduce_cert::check`] rebuilds every rule instance and checks the
//!    recorded `unless` conditions and the root's conflict status;
//! 2. [`std_deduce_cert::kernel_proof`] turns the monotone skeleton into
//!    kernel terms and has the kernel check every step.
//!
//! The two layers are printed separately, together with the side conditions
//! and whether a human must decide something. The process exits `0` only when
//! both layers pass, the root is proved and nothing is left open; `1` when
//! both layers pass but the root is a gap, an open obligation remains or a
//! recorded conflict is unresolved; and `2` when the file cannot be read or
//! parsed, or either layer fails. A logical pass with a kernel failure is
//! therefore a `2`, never a `0`.

use std::io::{self, BufRead, Write};

use std_deduce_cert::{render, Certificate, CheckReport, Node as CertNode, ObligationKind};
use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::env::{Ctx, DeclKind, Env, SourceRef};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{check, Expr};
use std_deduce_lang::{elab, Library};
use std_deduce_reason::{
    certificate as reason_certificate, Conflict, Provenance, Reasoner, Resolution, Side,
};

/// How a query ended. Only `Proved` is a success; the other two make the
/// process exit non-zero, the way a failed `check` does.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Outcome {
    Proved,
    Gap,
    Unresolved,
}

impl Outcome {
    /// The process exit code this outcome stands for. Only `Proved` is `0`;
    /// both a gap and an unresolved conflict mean the query was not proved.
    fn exit_code(self) -> i32 {
        match self {
            Outcome::Proved => 0,
            Outcome::Gap | Outcome::Unresolved => 1,
        }
    }
}

struct Session {
    lib: Library,
    /// Whether a theory has been loaded. `:check` needs an environment, so it
    /// refuses to run before any `:load`.
    loaded: bool,
}

impl Session {
    fn new() -> Self {
        Session {
            lib: Library::new(),
            loaded: false,
        }
    }

    fn handle(&mut self, line: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let line = line.trim();
        if line.is_empty() || line.starts_with("--") {
            return Ok(Outcome::Proved);
        }
        if let Some(rest) = line.strip_prefix(':') {
            let (cmd, arg) = rest.split_once(char::is_whitespace).unwrap_or((rest, ""));
            let arg = arg.trim();
            match cmd {
                "load" => {
                    let src = std::fs::read_to_string(arg)
                        .map_err(|e| format!("读取 `{arg}` 失败：{e}"))?;
                    let report = self.lib.load(arg, &src).map_err(|e| e.to_string())?;
                    self.loaded = true;
                    writeln!(out, "已加载 `{arg}`。").ok();
                    for d in &report.declared {
                        writeln!(out, "  + {d}").ok();
                    }
                    for c in &report.checked {
                        writeln!(out, "  ✓ {c}").ok();
                    }
                    for s in &report.shown {
                        writeln!(out, "  · {s}").ok();
                    }
                    Ok(Outcome::Proved)
                }
                "inspect" => {
                    for decl in self.lib.env.iter() {
                        let kind = match &decl.kind {
                            DeclKind::Sort => "sort ",
                            DeclKind::Obj => "obj  ",
                            DeclKind::Pred => "pred ",
                            DeclKind::Axiom => "axiom",
                            DeclKind::Def { .. } => "def  ",
                            DeclKind::Rule(_) => "rule ",
                            DeclKind::Interpretation(_) => "interp",
                            DeclKind::Contrary { .. } => "contr ",
                            DeclKind::Unique { .. } => "uniq  ",
                        };
                        writeln!(out, "  {kind} {} : {}", decl.name, print_expr(&decl.ty)).ok();
                        for s in &decl.sources {
                            writeln!(out, "       ← {}", s.one_line()).ok();
                        }
                    }
                    Ok(Outcome::Proved)
                }
                "given" => {
                    let t = parse_term(arg)?;
                    let e = elab::elab_top(&self.lib.env, &t).map_err(|e| e.msg)?;
                    check::check(&self.lib.env, &Ctx::new(), &e, &Expr::Sort(0))
                        .map_err(|e| e.to_string())?;
                    writeln!(out, "已登记假设：{}", print_expr(&e)).ok();
                    // Stash it on the library as an assumption of the current
                    // session, recorded as a declaration for auditability.
                    let mut lib = self.lib.clone();
                    let name = format!("已知{}", lib.env.len());
                    let decl = std_deduce_kernel::Decl {
                        name: std_deduce_kernel::name(&name),
                        kind: DeclKind::Axiom,
                        ty: e,
                        sources: vec![SourceRef {
                            text: "用户输入".into(),
                            locator: String::new(),
                            ..Default::default()
                        }],
                        index: 0,
                    };
                    lib.env
                        .insert(decl, &Ctx::new())
                        .map_err(|e| e.to_string())?;
                    self.lib = lib;
                    Ok(Outcome::Proved)
                }
                "why" | "gap" => self.query(cmd, arg, out),
                "cert" => self.export_certificate(arg, out),
                "check" => self.check_certificate(arg, out),
                "quit" | "exit" => Ok(Outcome::Proved),
                other => Err(format!("未知命令 `:{other}`")),
            }
        } else {
            // Bare line: treated as a command.
            self.handle(&format!(":{line}"), out)
        }
    }

    fn query(&mut self, cmd: &str, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let goal = self.goal(arg)?;
        let mut r = Reasoner::new(&self.lib.env);
        // Every axiom whose declared type is a proposition is usable as an
        // assumption. This is how a corpus of facts enters. See
        // `Reasoner::assume_ledger_axioms`.
        r.assume_ledger_axioms()?;
        r.saturate()?;

        // A conclusion can be in a recorded conflict without being asserted:
        // that is a third outcome, distinct from both success and a gap.
        if let Some(c) = r.conflict_for(&goal) {
            match &c.resolution {
                Resolution::Unresolved => {
                    report_unresolved(out, &r, &goal, &c);
                    return Ok(Outcome::Unresolved);
                }
                Resolution::Defeated { winner } => {
                    let side = r.conflict_side(&c, &goal);
                    if side != Some(*winner) {
                        report_defeated(out, &r, &goal, &c, *winner);
                        return Ok(Outcome::Gap);
                    }
                    // The winner is asserted; fall through and show it as
                    // proved, with a note about the defeated competitor.
                    let reachable = r.knows(&goal);
                    debug_assert!(reachable);
                }
            }
        }

        let reachable = r.knows(&goal);

        if cmd == "gap" {
            let ex = r.explain(&goal);
            if reachable {
                writeln!(out, "目标可以推出。").ok();
                return Ok(Outcome::Proved);
            }
            writeln!(out, "无法推出 {}。以下是缺口：", print_expr(&goal)).ok();
            if let Some(n) = ex.note {
                writeln!(out, "  {n}").ok();
            }
            if ex.candidates.is_empty() {
                writeln!(
                    out,
                    "  没有任何规则以它为结论：要么补一条规则，要么把它作为已知事实登记。"
                )
                .ok();
            }
            for c in ex.candidates {
                writeln!(out, "  候选 ⟨{}⟩", c.rule).ok();
                for s in &c.sources {
                    writeln!(out, "    ← {}", s.one_line()).ok();
                }
                if !c.missing.is_empty() {
                    writeln!(
                        out,
                        "    缺：{}",
                        c.missing
                            .iter()
                            .map(print_expr)
                            .collect::<Vec<_>>()
                            .join("；")
                    )
                    .ok();
                }
                for b in &c.blocked_by {
                    writeln!(
                        out,
                        "    被阻断：「{}」已成立，故本规则不触发",
                        print_expr(b)
                    )
                    .ok();
                }
            }
            return Ok(Outcome::Gap);
        }

        let mut d = r.derivation();
        if reachable {
            d.root = r.root_for(&goal);
        } else {
            let ex = r.explain(&goal);
            let id = d.nodes.len();
            d.nodes.push(std_deduce_reason::Node::Gap {
                prop: goal.clone(),
                candidates: ex.candidates,
                note: ex.note,
            });
            d.root = Some(id);
        }

        let certificate = reason_certificate(&d)?;
        // The tree is printed from the certificate, then that same certificate
        // is checked by both layers: the tree the user sees and the object
        // being checked cannot diverge.
        writeln!(out, "{}", render(&certificate)?).ok();

        let checked = std_deduce_cert::check(&self.lib.env, &certificate);
        let kernel = std_deduce_cert::kernel_proof(&self.lib.env, &certificate);
        let (report, kernel_report) = match (checked, kernel) {
            (Ok(report), Ok(kernel)) => (report, kernel),
            (checked, kernel) => {
                let mut failures = Vec::new();
                if let Err(error) = checked {
                    writeln!(out, "逻辑校验失败：{error}").ok();
                    failures.push(format!("逻辑层：{error}"));
                }
                if let Err(error) = kernel {
                    writeln!(out, "内核证明失败：{error}").ok();
                    failures.push(format!("内核层：{error}"));
                }
                return Err(format!("证书校验失败（{}）", failures.join("；")));
            }
        };

        let root = certificate
            .root
            .ok_or_else(|| "推理器生成的证书没有根节点：无法确认结论".to_owned())?;
        if matches!(certificate.nodes.get(root), Some(CertNode::Gap { .. })) {
            writeln!(out, "证书有效，但根为缺口，结论未被证明。").ok();
            report_conflicts(out, &certificate);
            return Ok(Outcome::Gap);
        }
        if !report.root_proved || !kernel_report.root_proved {
            writeln!(out, "证书有效，但根未被证明，结论未被证明。").ok();
            report_conflicts(out, &certificate);
            return Ok(Outcome::Gap);
        }

        let unresolved = certificate
            .conflicts
            .iter()
            .filter(|conflict| {
                matches!(conflict.resolution, std_deduce_cert::Resolution::Unresolved)
            })
            .count();
        if !certificate.open_obligations.is_empty() || unresolved > 0 {
            writeln!(
                out,
                "证书有效且根已证明，但仍有未决义务（open_obligations {} 项，未决冲突 {} 项），不能报告为无保留的证明。",
                certificate.open_obligations.len(),
                unresolved
            )
            .ok();
            report_conflicts(out, &certificate);
            return Ok(Outcome::Gap);
        }

        // Determine the defeated-conflict note before printing the success
        // line: a comparison failure is an error, never a success followed by
        // an error.
        let won_conflict = if reachable {
            won_conflict_note(&self.lib.env, &goal, &certificate)?
        } else {
            None
        };

        writeln!(out, "推导已通过独立校验。").ok();
        report_conflicts(out, &certificate);
        if let Some(other) = won_conflict {
            writeln!(
                out,
                "注：与「{}」存在冲突，已按记录的裁决为本结论胜出（裁决依据与优先级来源未核验）。",
                print_expr(&other)
            )
            .ok();
        }
        Ok(Outcome::Proved)
    }

    /// Parse `arg` as a proposition in the current environment.
    fn goal(&self, arg: &str) -> Result<Expr, String> {
        let t = parse_term(arg)?;
        let goal = elab::elab_top(&self.lib.env, &t).map_err(|e| e.msg)?;
        check::check(&self.lib.env, &Ctx::new(), &goal, &Expr::Sort(0))
            .map_err(|e| format!("目标不是命题：{e}"))?;
        Ok(goal)
    }

    /// Derive `arg` and print its certificate as pretty JSON.
    ///
    /// A proved goal has that proof as the root. An unreachable goal gets a
    /// gap node as the root, with the same candidates `:gap` would report, so
    /// the exported certificate is still checkable and says `root_proved
    /// = false` rather than pretending to be a proof.
    fn export_certificate(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if arg.is_empty() {
            return Err("用法：:cert <目标命题>".into());
        }
        let goal = self.goal(arg)?;
        let mut r = Reasoner::new(&self.lib.env);
        r.assume_ledger_axioms()?;
        r.saturate()?;

        let reachable = r.knows(&goal);
        let mut d = r.derivation();
        if reachable {
            d.root = r.root_for(&goal);
        } else {
            let ex = r.explain(&goal);
            let id = d.nodes.len();
            d.nodes.push(std_deduce_reason::Node::Gap {
                prop: goal.clone(),
                candidates: ex.candidates,
                note: ex.note,
            });
            d.root = Some(id);
        }

        let certificate = reason_certificate(&d)?;
        let json = certificate
            .to_json_pretty()
            .map_err(|e| format!("证书序列化失败：{e}"))?;
        writeln!(out, "{json}").ok();
        Ok(if reachable {
            Outcome::Proved
        } else {
            Outcome::Gap
        })
    }

    /// Check a certificate against the loaded environment, without rerunning
    /// the reasoner.
    ///
    /// Both layers run and are reported separately: `cert::check` rebuilds
    /// rule instances and side conditions, then `kernel_proof` rebuilds the
    /// monotone proof terms and asks the kernel. A logical pass with a kernel
    /// failure is an error (`2`), not a valid certificate.
    fn check_certificate(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !self.loaded {
            write_check_not_run(out, "尚未加载理论");
            return Err("尚未加载理论：:check 需要环境才能校验证书，请先 :load <文件>".into());
        }
        if arg.is_empty() {
            return Err("用法：:check <证书文件>".into());
        }
        let text = match std::fs::read_to_string(arg) {
            Ok(text) => text,
            Err(e) => {
                write_check_not_run(out, "读取证书失败");
                return Err(format!("读取证书 `{arg}` 失败：{e}"));
            }
        };
        let certificate = match Certificate::from_json(&text) {
            Ok(certificate) => certificate,
            Err(e) => {
                write_check_not_run(out, "证书 JSON 无效");
                return Err(format!("证书 `{arg}` 不是有效的证书 JSON：{e}"));
            }
        };

        // Layer 1: rebuild every rule instance from its own evidence and check
        // the recorded `unless` conditions and the root's conflict status.
        let report = match std_deduce_cert::check(&self.lib.env, &certificate) {
            Ok(report) => report,
            Err(e) => {
                writeln!(out, "逻辑校验：失败（{e}）").ok();
                writeln!(out, "内核证明：未运行（逻辑校验失败）").ok();
                writeln!(out, "侧条件：未评估（逻辑校验失败）").ok();
                writeln!(out, "需人判断：未评估（逻辑校验失败）").ok();
                return Err(format!("证书校验失败（逻辑层）：{e}"));
            }
        };
        writeln!(
            out,
            "逻辑校验：通过（检查 {} 个节点；{}）",
            report.nodes_checked,
            root_summary(&certificate, &report)
        )
        .ok();

        // Layer 2: the monotone skeleton must survive the kernel, not only the
        // structural check above.
        let kernel = match std_deduce_cert::kernel_proof(&self.lib.env, &certificate) {
            Ok(kernel) => kernel,
            Err(e) => {
                writeln!(out, "内核证明：失败（{e}）").ok();
                writeln!(out, "侧条件：未评估（内核证明失败）").ok();
                writeln!(out, "需人判断：未评估（内核证明失败）").ok();
                return Err(format!("证书校验失败（内核层）：{e}"));
            }
        };
        writeln!(
            out,
            "内核证明：通过（{} 个规则步骤；{}）",
            kernel.steps.len(),
            if kernel.root_proved {
                "根证明项通过内核"
            } else {
                "根为缺口，无证明项"
            }
        )
        .ok();

        let unresolved = certificate
            .conflicts
            .iter()
            .filter(|conflict| {
                matches!(conflict.resolution, std_deduce_cert::Resolution::Unresolved)
            })
            .count();
        let requires_human = report.requires_human || unresolved > 0;

        writeln!(
            out,
            "侧条件：unless 未发现已成立的阻断条件；未决冲突 {} 项；{}优先级来源未核验",
            unresolved,
            if report.conflict_resolved {
                "根冲突已按记录裁决；"
            } else {
                ""
            }
        )
        .ok();
        writeln!(
            out,
            "需人判断：{}",
            human_summary(&certificate, requires_human, unresolved)
        )
        .ok();

        // A root is successful only when both layers agree on it and nothing
        // is left to a human or an unresolved conflict.
        let proved = report.root_proved && kernel.root_proved && !requires_human && unresolved == 0;
        Ok(if proved {
            Outcome::Proved
        } else {
            Outcome::Gap
        })
    }
}

/// Print the four labelled lines when `:check` cannot reach either layer.
fn write_check_not_run(out: &mut impl Write, reason: &str) {
    writeln!(out, "逻辑校验：未运行（{reason}）").ok();
    writeln!(out, "内核证明：未运行（{reason}）").ok();
    writeln!(out, "侧条件：未评估（{reason}）").ok();
    writeln!(out, "需人判断：未评估（{reason}）").ok();
}

/// Describe what the logical layer established about the root.
fn root_summary(certificate: &Certificate, report: &CheckReport) -> String {
    match certificate.root {
        None => "没有根节点".to_owned(),
        Some(root) if matches!(certificate.nodes[root], CertNode::Gap { .. }) => {
            "根未被证明，根为缺口".to_owned()
        }
        Some(_) if report.root_proved && report.root_is_assumption => {
            format!(
                "根已证明，根为假设，证书共 {} 条假设",
                report.assumption_count
            )
        }
        Some(_) if report.root_proved => {
            format!(
                "根已证明，根为规则推导，证书共 {} 条假设",
                report.assumption_count
            )
        }
        Some(_) => "根未被证明".to_owned(),
    }
}

/// Explain why a human is or is not needed, using the recorded obligations.
fn human_summary(certificate: &Certificate, requires_human: bool, unresolved: usize) -> String {
    if !requires_human {
        return "否（无未决义务）".to_owned();
    }
    let mut counts: std::collections::BTreeMap<&'static str, usize> =
        std::collections::BTreeMap::new();
    for obligation in &certificate.open_obligations {
        *counts
            .entry(obligation_kind_label(obligation.kind))
            .or_default() += 1;
    }
    let mut details: Vec<String> = counts
        .iter()
        .map(|(label, count)| format!("{label} {count} 项"))
        .collect();
    if details.is_empty() || (unresolved > 0 && !counts.contains_key("冲突未决")) {
        details.push(format!("未决冲突 {unresolved} 项"));
    }
    format!(
        "是（open_obligations {} 项：{}）",
        certificate.open_obligations.len(),
        details.join("、")
    )
}

/// The user-facing label of an obligation kind.
fn obligation_kind_label(kind: ObligationKind) -> &'static str {
    match kind {
        ObligationKind::MissingPremise => "缺少前提",
        ObligationKind::MissingSource => "缺少来源",
        ObligationKind::OpenConcept => "开放概念",
        ObligationKind::UnresolvedConflict => "冲突未决",
        ObligationKind::NeedsHumanDetermination => "需人判断",
        ObligationKind::Other => "其他",
    }
}

fn report_unresolved(out: &mut impl Write, r: &Reasoner, goal: &Expr, c: &Conflict) {
    writeln!(out, "冲突未决：{}", print_expr(goal)).ok();
    writeln!(
        out,
        "  该结论没有进入事实库——系统不替你选，但也绝不悄悄丢掉它。"
    )
    .ok();
    writeln!(
        out,
        "  左：{}  ← {}",
        print_expr(&c.left),
        describe(&c.left_by)
    )
    .ok();
    writeln!(
        out,
        "  右：{}  ← {}",
        print_expr(&c.right),
        describe(&c.right_by)
    )
    .ok();
    for (label, prop) in [("左", &c.left), ("右", &c.right)] {
        writeln!(out, "── 冲突{label}方：{} ──", print_expr(prop)).ok();
        show_derivation(out, r, prop);
    }
}

fn report_defeated(out: &mut impl Write, r: &Reasoner, goal: &Expr, c: &Conflict, winner: Side) {
    let (win, win_by) = match winner {
        Side::Left => (&c.left, &c.left_by),
        Side::Right => (&c.right, &c.right_by),
    };
    writeln!(
        out,
        "冲突已裁决：{} 与 {} 不能并存",
        print_expr(&c.left),
        print_expr(&c.right)
    )
    .ok();
    writeln!(
        out,
        "  本结论「{}」被否决；胜出的是「{}」（{}）。",
        print_expr(goal),
        print_expr(win),
        describe(win_by)
    )
    .ok();
    writeln!(out, "── 胜出方推导：{} ──", print_expr(win)).ok();
    show_derivation(out, r, win);
    writeln!(out, "── 被否决方推导：{} ──", print_expr(goal)).ok();
    show_derivation(out, r, goal);
}

fn show_derivation(out: &mut impl Write, r: &Reasoner, prop: &Expr) {
    let Some(d) = r.derivation_for(prop) else {
        writeln!(out, "  （推导无法重建：它的前提本身已不在事实库）").ok();
        return;
    };
    let certificate = match reason_certificate(&d) {
        Ok(certificate) => certificate,
        Err(error) => {
            writeln!(out, "  （该推导未能生成证书：{error}）").ok();
            return;
        }
    };
    match render(&certificate) {
        Ok(rendered) => writeln!(out, "{rendered}").ok(),
        Err(error) => {
            writeln!(out, "  （该推导的证书无法渲染：{error}）").ok();
            return;
        }
    };
    match std_deduce_cert::check(r.env(), &certificate) {
        Ok(report) if report.root_proved => {
            writeln!(out, "  （该推导通过证书逻辑校验）").ok();
        }
        Ok(_) => {
            writeln!(out, "  （该推导未通过证书逻辑校验：根未被证明）").ok();
        }
        Err(error) => {
            writeln!(out, "  （该推导未通过证书逻辑校验：{error}）").ok();
        }
    }
}

/// Print every conflict the certificate records.
fn report_conflicts(out: &mut impl Write, certificate: &Certificate) {
    for conflict in &certificate.conflicts {
        let how = match conflict.resolution {
            std_deduce_cert::Resolution::Unresolved => "未决",
            std_deduce_cert::Resolution::Defeated { .. } => "已裁决",
        };
        writeln!(
            out,
            "冲突（{how}）：{} 与 {}",
            print_expr(&Expr::from(&conflict.left)),
            print_expr(&Expr::from(&conflict.right))
        )
        .ok();
    }
}

/// The defeated competitor of a conflict the queried proposition won.
///
/// The proposition is matched with kernel definitional equality, not by
/// comparing printed strings.
fn won_conflict_note(
    env: &Env,
    goal: &Expr,
    certificate: &Certificate,
) -> Result<Option<Expr>, String> {
    for conflict in &certificate.conflicts {
        let left = Expr::from(&conflict.left);
        let right = Expr::from(&conflict.right);
        let side = if convertible(env, &Ctx::new(), goal, &left)
            .map_err(|error| format!("无法比较目标与冲突左命题：{error}"))?
        {
            Some(std_deduce_cert::Side::Left)
        } else if convertible(env, &Ctx::new(), goal, &right)
            .map_err(|error| format!("无法比较目标与冲突右命题：{error}"))?
        {
            Some(std_deduce_cert::Side::Right)
        } else {
            None
        };
        let (Some(side), std_deduce_cert::Resolution::Defeated { winner }) =
            (side, &conflict.resolution)
        else {
            continue;
        };
        if side != *winner {
            continue;
        }
        let other = match winner {
            std_deduce_cert::Side::Left => &conflict.right,
            std_deduce_cert::Side::Right => &conflict.left,
        };
        return Ok(Some(Expr::from(other)));
    }
    Ok(None)
}

fn describe(p: &Provenance) -> String {
    match p {
        Provenance::Assumption => "已知事实".into(),
        Provenance::Rules(rs) if rs.is_empty() => "已无可重建的规则实例".into(),
        Provenance::Rules(rs) => format!(
            "规则 {}",
            rs.iter()
                .map(|r| format!("⟨{r}⟩"))
                .collect::<Vec<_>>()
                .join("、")
        ),
    }
}

fn parse_term(s: &str) -> Result<std_deduce_lang::ast::Term, String> {
    // Wrap a bare term as `#check <term>`, which is the one place the
    // grammar admits a bare expression at the top level.
    let src = format!("#check {s}");
    let toks = std_deduce_lang::lexer::lex(&src).map_err(|e| e.to_string())?;
    let mut p = std_deduce_lang::parser::Parser::new(toks);
    // Skip the `#` and `check` tokens by parsing the program and taking the
    // command, keeping the parser's own recovery in one place.
    let items = p.program().map_err(|e| e.to_string())?;
    match items.into_iter().next() {
        Some(std_deduce_lang::ast::Item::Check(t)) => Ok(t),
        _ => Err("无法解析为项".into()),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut session = Session::new();
    let mut out = io::stdout();

    // Non-interactive: run every argument as a command.
    if args.len() > 1 {
        let mut worst = 0;
        for a in &args[1..] {
            match session.handle(a, &mut out) {
                Ok(o) => worst = worst.max(o.exit_code()),
                Err(e) => {
                    eprintln!("错误：{e}");
                    std::process::exit(2);
                }
            }
        }
        if worst != 0 {
            std::process::exit(worst);
        }
        return;
    }

    println!("std-deduce 0.1 — 输入 :help 查看命令。");
    let stdin = io::stdin();
    let mut worst = 0;
    for line in stdin.lock().lines() {
        let Ok(line) = line else { break };
        if line.trim() == ":quit" || line.trim() == ":exit" {
            break;
        }
        if line.trim() == ":help" {
            println!(
                ":load <文件>  :inspect  :given <命题>  :why <命题>  :gap <命题>  \
                 :cert <命题>  :check <证书文件>  :quit"
            );
            continue;
        }
        match session.handle(&line, &mut out) {
            Ok(outcome) => worst = worst.max(outcome.exit_code()),
            Err(e) => {
                println!("错误：{e}");
                worst = 2;
            }
        }
    }
    // Interactive mode used to ignore every result; stdin input now settles
    // the exit code on the worst command, the same way argv mode does.
    if worst != 0 {
        std::process::exit(worst);
    }
}
