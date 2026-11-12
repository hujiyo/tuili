//! Command-line interface.
//!
//! Commands are line-oriented:
//!
//! ```text
//! :load <file>            load a theory file
//! :inspect                dump the ledger
//! :why <term>             derive, print the tree, and verify it
//! :gap <term>             explain what is missing for a goal
//! :given <term>           add an assumption by hand
//! :quit
//! ```

use std::io::{self, BufRead, Write};

use std_deduce_kernel::env::{Ctx, DeclKind, SourceRef};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{check, Expr};
use std_deduce_lang::{elab, Library};
use std_deduce_reason::{render, verify, Reasoner};

struct Session {
    lib: Library,
}

impl Session {
    fn new() -> Self {
        Session { lib: Library::new() }
    }

    fn handle(&mut self, line: &str, out: &mut impl Write) -> Result<(), String> {
        let line = line.trim();
        if line.is_empty() || line.starts_with("--") {
            return Ok(());
        }
        if let Some(rest) = line.strip_prefix(':') {
            let (cmd, arg) = rest.split_once(char::is_whitespace).unwrap_or((rest, ""));
            let arg = arg.trim();
            match cmd {
                "load" => {
                    let src = std::fs::read_to_string(arg)
                        .map_err(|e| format!("读取 `{arg}` 失败：{e}"))?;
                    let report = self
                        .lib
                        .load(arg, &src)
                        .map_err(|e| e.to_string())?;
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
                    Ok(())
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
                        };
                        writeln!(
                            out,
                            "  {kind} {} : {}",
                            decl.name,
                            print_expr(&decl.ty)
                        )
                        .ok();
                        for s in &decl.sources {
                            writeln!(out, "       ← {}", s.one_line()).ok();
                        }
                    }
                    Ok(())
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
                    Ok(())
                }
                "why" | "gap" => {
                    let t = parse_term(arg)?;
                    let goal = elab::elab_top(&self.lib.env, &t).map_err(|e| e.msg)?;
                    check::check(&self.lib.env, &Ctx::new(), &goal, &Expr::Sort(0))
                        .map_err(|e| format!("目标不是命题：{e}"))?;
                    let mut r = Reasoner::new(&self.lib.env);
                    // Every axiom whose declared type is a proposition is
                    // usable as an assumption. This is how a corpus of facts
                    // enters. See `Reasoner::assume_ledger_axioms`.
                    r.assume_ledger_axioms()?;
                    r.saturate()?;
                    let mut d = r.derivation();

                    let reachable = r.knows(&goal);

                    if cmd == "gap" {
                        let ex = r.explain(&goal);
                        if reachable {
                            writeln!(out, "目标可以推出。").ok();
                        } else {
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
                        }
                        return Ok(());
                    }

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

                    writeln!(out, "{}", render(&self.lib.env, &d)).ok();
                    // Verification is independent of the reasoner.
                    match verify(&self.lib.env, &d) {
                        Ok(()) => {
                            writeln!(out, "推导已通过独立校验。").ok();
                        }
                        Err(e) => {
                            writeln!(out, "独立校验失败：{e}").ok();
                        }
                    }
                    for c in &d.conflicts {
                        writeln!(
                            out,
                            "冲突：{} 与 {}（{}/{:?}）",
                            print_expr(&c.left),
                            print_expr(&c.right),
                            c.left_rule,
                            c.resolution
                        )
                        .ok();
                    }
                    Ok(())
                }
                "quit" | "exit" => Ok(()),
                other => Err(format!("未知命令 `:{other}`")),
            }
        } else {
            // Bare line: treated as a command.
            self.handle(&format!(":{line}"), out)
        }
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
        for a in &args[1..] {
            match session.handle(a, &mut out) {
                Ok(()) => {}
                Err(e) => {
                    eprintln!("错误：{e}");
                    std::process::exit(1);
                }
            }
        }
        return;
    }

    println!("std-deduce 0.1 — 输入 :help 查看命令。");
    let stdin = io::stdin();
    for line in stdin.lock().lines() {
        let Ok(line) = line else { break };
        if line.trim() == ":quit" || line.trim() == ":exit" {
            break;
        }
        if line.trim() == ":help" {
            println!(":load <文件>  :inspect  :given <命题>  :why <命题>  :gap <命题>  :quit");
            continue;
        }
        match session.handle(&line, &mut out) {
            Ok(()) => {}
            Err(e) => println!("错误：{e}"),
        }
    }
}
