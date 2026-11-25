//! Recursive-descent parser for Lean-style surface syntax.
//!
//! Grammar (summary):
//!
//! ```text
//! program  := import* namespace? item*
//! import   := 'import' PACK                (before namespace and all items)
//! namespace := 'namespace' NAMESPACE      (first non-import item only)
//! item     := sort | pred | axiom | def | rule | interpret | contrary | unique | open | priority | command
//! sort     := 'sort' IDENT source?
//! pred     := 'pred' IDENT ':' term source?
//! axiom    := 'axiom' IDENT ':' term
//!             (source | 'identity' KEYWORD | 'occurred_at' DATE | 'occurred_in' CODE)*
//!             -- source and identity each at most once, in either order;
//!             -- identity must start its own line: 'identity' KEYWORD
//! def      := 'def' IDENT ':' term ':=' term source?
//! rule     := 'rule' IDENT clause+
//! clause   := 'params' binder (',' binder)*
//!           | 'premise' (binder ':')? term
//!           | 'conclude' term
//!           | 'unless' term
//!           | 'defeated_by' IDENT
//!           | 'prefer' IDENT
//!           | 'burden' burden_value
//!           | 'standard' standard_value
//!           | 'exception_burden' burden_value
//!           | 'exception_standard' standard_value
//!           | 'source' (source_key STRING)+
//!           | 'effective' DATE | 'repealed' DATE
//!           | 'jurisdiction' CODE | 'territory' CODE
//! interpret := 'interpret' IDENT ':' application '→' application
//!              'direction' DIRECTION 'source' (source_key STRING)+
//!           -- `direction` is required and must start its own line, as must
//!           -- every source clause (at least one is required and text,
//!           -- locator and version must be non-empty). Both sides are
//!           -- application terms: an arrow inside one needs parentheses.
//! burden_value   := 'claimant' | 'respondent' | 'court'
//! standard_value := 'preponderance' | 'clear_and_convincing'
//!                 | 'beyond_reasonable_doubt'
//! priority := 'priority' IDENT 'over' IDENT source*
//! open     := 'open' IDENT
//!           -- marks an already declared (or later declared in the same file)
//!           -- predicate as an open concept; the target is checked on load
//! DIRECTION := 'literal' | 'expand' | 'narrow' | 'analogy'
//! source_key := 'text' | 'locator' | 'version' | 'effective' | 'quote' | 'url'
//!           | 'jurisdiction' | 'retrieved_at' | 'hash' | 'note'
//! DATE     := IDENT matching YYYY-MM-DD (validated on load)
//! CODE     := IDENT matching the manifest jurisdiction/territory code
//! term     := arrow
//! arrow    := app ('→' term)?
//! app      := atom atom*
//! atom     := IDENT | '(' term ')' | '∀' binder ',' term | 'fun' binder '=>' term
//!         | 'Prop' | 'Type' NUM?
//! ```
//!
//! The parser is line-oriented at the item/clause level: a newline ends a
//! clause unless a term is syntactically incomplete. This keeps rule blocks
//! looking like prose, which is what a legal reader needs.

use std_deduce_kernel::{Burden, FactIdentity, InterpretationDirection, Standard};

use crate::ast::*;
use crate::lexer::{Tok, Token};

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
    /// Current recursive `term()` depth, used to reject adversarially nested
    /// input before the stack overflows.
    depth: usize,
}

pub type PResult<T> = Result<T, ParseError>;

/// The maximum recursive nesting depth of one term.
///
/// Each parenthesis, arrow, `∀` or `λ` calls `term()` again; without a bound a
/// file of a few thousand `(` characters overflows the stack. 64 levels are
/// far more than any readable legal formula needs. Exceeding the bound is a
/// parse error at the offending token, never a panic.
pub const MAX_TERM_DEPTH: usize = 64;

/// The maximum number of arguments in one application spine (`f a b c`).
///
/// A long spine builds a left-nested term; the bound keeps elaboration and
/// kernel checking away from pathologically deep trees. It does not limit
/// useful arity: no declaration has more than a handful of arguments.
pub const MAX_APPLICATION_ARITY: usize = 64;

/// The maximum number of binders (parameters plus premises) in one rule.
///
/// The kernel turns the rule telescope into a nested function type and checks
/// it recursively; proof search also backtracks over one stack frame per
/// premise. A bound on the *total* telescope protects both. It is deliberately
/// small: a legal rule has a handful of binders, while a few hundred already
/// overflow the CLI's main-thread stack on Windows.
pub const MAX_RULE_BINDERS: usize = 64;

#[derive(Debug, Clone)]
pub struct ParseError {
    pub msg: String,
    pub line: usize,
    pub col: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "第 {} 行第 {} 列：{}", self.line, self.col, self.msg)
    }
}
impl std::error::Error for ParseError {}

/// The retired `#assert` command must not stay as a silent alias: it only
/// checked the term's type, so the old name suggested a proof that never
/// happened. Parsing it now points at the renamed command and at what the
/// renamed command does not do.
const ASSERT_RENAMED: &str = concat!(
    "`#assert` 已改名为 `#proposition`（裸 `assert` 相应改为 `proposition`）。",
    "`#proposition` 只检查该项的类型是否为 Prop，不证明命题成立；",
    "要断言成立请用事实（`axiom` / `:given`）或规则（`rule`）。"
);

/// The keys a structured `source` clause accepts.
const SOURCE_KEYS: &[&str] = &[
    "text",
    "locator",
    "version",
    "effective",
    "quote",
    "url",
    "jurisdiction",
    "retrieved_at",
    "hash",
    "note",
];

fn is_source_key(name: &str) -> bool {
    SOURCE_KEYS.contains(&name)
}

/// A rule-body scope clause keyword that also happens to be a `source` key.
fn is_scope_clause_key(name: &str) -> bool {
    matches!(name, "effective" | "jurisdiction" | "territory")
}

/// Why a namespace is malformed, or `None` when it is well formed.
///
/// A namespace is lowercase ASCII letters, digits, `.` and `-`; every
/// dot-separated segment is non-empty and may not start or end with `-`.
fn namespace_format_error(ns: &str) -> Option<String> {
    if ns.is_empty() {
        return Some("命名空间不能为空".into());
    }
    for ch in ns.chars() {
        if !(ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '.' || ch == '-') {
            return Some(format!(
                "命名空间 `{ns}` 含非法字符 `{ch}`：只能使用小写 ASCII 字母、数字、`.` 和 `-`"
            ));
        }
    }
    for segment in ns.split('.') {
        if segment.is_empty() {
            return Some(format!("命名空间 `{ns}` 含空段：`.` 之间必须有内容"));
        }
        if segment.starts_with('-') || segment.ends_with('-') {
            return Some(format!(
                "命名空间 `{ns}` 的段 `{segment}` 不能以 `-` 开头或结尾"
            ));
        }
    }
    None
}

impl Parser {
    pub fn new(toks: Vec<Token>) -> Self {
        Parser {
            toks,
            pos: 0,
            depth: 0,
        }
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn peek_at(&self, n: usize) -> &Tok {
        let i = (self.pos + n).min(self.toks.len() - 1);
        &self.toks[i].tok
    }
    fn here(&self) -> &Token {
        &self.toks[self.pos.min(self.toks.len() - 1)]
    }
    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        self.pos += 1;
        t
    }
    fn err<T>(&self, msg: impl Into<String>) -> PResult<T> {
        Err(ParseError {
            msg: msg.into(),
            line: self.here().line,
            col: self.here().col,
        })
    }
    /// An error reported at an earlier, caller-chosen position. Used when the
    /// parser has already moved past the token that caused the problem (for
    /// example, an interpretation's header once a clause is missing).
    fn err_at<T>(&self, line: usize, col: usize, msg: impl Into<String>) -> PResult<T> {
        Err(ParseError {
            msg: msg.into(),
            line,
            col,
        })
    }
    fn expect(&mut self, t: &Tok, what: &str) -> PResult<()> {
        if self.peek() == t {
            self.bump();
            Ok(())
        } else {
            self.err(format!("期望 {what}，实际是 `{:?}`", self.peek()))
        }
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == t {
            self.bump();
            true
        } else {
            false
        }
    }
    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline) {
            self.bump();
        }
    }
    fn ident(&mut self) -> PResult<String> {
        match self.bump() {
            Tok::Ident(s) => Ok(s),
            other => self.err(format!("期望标识符，实际是 `{other:?}`")),
        }
    }
    /// A keyword used in item position.
    fn keyword(&mut self, kw: &str) -> bool {
        matches!(self.peek(), Tok::Ident(s) if s == kw)
    }

    pub fn program(&mut self) -> PResult<Vec<Item>> {
        let mut items = Vec::new();
        let mut namespace_seen = false;
        loop {
            self.skip_newlines();
            if matches!(self.peek(), Tok::Eof) {
                break;
            }
            // `import` opens the file: it may follow only other imports
            // (blank lines are skipped above), never the namespace or a
            // declaration.
            let only_imports_so_far = items.iter().all(|item| matches!(item, Item::Import(_)));
            if self.keyword("import") {
                if !only_imports_so_far {
                    return self.err("import 只能出现在 namespace 和所有声明之前");
                }
                items.push(self.item()?);
                continue;
            }
            if self.keyword("namespace") {
                if namespace_seen {
                    return self.err("namespace 只能出现一次");
                }
                if !only_imports_so_far {
                    return self.err("namespace 必须是文件的第一条声明，不能出现在其他声明之后");
                }
                namespace_seen = true;
            }
            items.push(self.item()?);
        }
        Ok(items)
    }

    fn item(&mut self) -> PResult<Item> {
        // Commands may be written `#check` or `# check`. The lexer emits the
        // sigil as its own token, so if we see one we consume both here and
        // remember that the keyword is already gone from the stream.
        let (kw, already_bumped) = if self.peek() == &Tok::Ident("#".into()) {
            self.bump();
            (self.ident()?, true)
        } else {
            match self.peek().clone() {
                Tok::Ident(s) => (s, false),
                other => {
                    return self.err(format!("期望声明关键字，实际是 `{other:?}`"));
                }
            }
        };
        match kw.as_str() {
            "check" | "why" | "gap" | "proposition" | "assert" | "show" if already_bumped => {
                self.dispatch_command(&kw)
            }
            _ if already_bumped => self.err(format!("未知命令 `#{kw}`")),
            _ => self.dispatch_plain(&kw),
        }
    }

    fn dispatch_command(&mut self, kw: &str) -> PResult<Item> {
        match kw {
            "check" => Ok(Item::Check(self.term()?)),
            "why" => Ok(Item::Why(self.term()?)),
            "gap" => Ok(Item::Gap(self.term()?)),
            "proposition" => Ok(Item::Proposition(self.term()?)),
            "assert" => {
                // `item` consumed the sigil and the command name, so the
                // sigil sits two tokens back. Report there: the user needs to
                // change the command, not its term.
                let sigil = &self.toks[self.pos - 2];
                Err(ParseError {
                    msg: ASSERT_RENAMED.into(),
                    line: sigil.line,
                    col: sigil.col,
                })
            }
            "show" => Ok(Item::Show(self.ident()?)),
            other => self.err(format!("未知命令 `#{other}`")),
        }
    }

    /// Dispatch an un-sigiled keyword. This is the bulk of `item`, split out
    /// so the `#`-command path above stays short.
    fn dispatch_plain(&mut self, kw: &str) -> PResult<Item> {
        match kw {
            "import" => {
                // Report a bare `import` at the keyword itself; after the
                // bump `here()` would point at the newline or next item.
                let (line, col) = {
                    let token = self.here();
                    (token.line, token.col)
                };
                self.bump();
                let pack = match self.peek().clone() {
                    Tok::Ident(pack) => {
                        self.bump();
                        pack
                    }
                    other => {
                        return Err(ParseError {
                            msg: format!("`import` 之后必须是包名，实际是 `{other:?}`"),
                            line,
                            col,
                        });
                    }
                };
                if !matches!(self.peek(), Tok::Newline | Tok::Eof) {
                    return self.err(format!(
                        "`import {pack}` 之后必须是换行，实际是 `{:?}`",
                        self.peek()
                    ));
                }
                Ok(Item::Import(pack))
            }
            "namespace" => {
                self.bump();
                let (line, col) = {
                    let token = self.here();
                    (token.line, token.col)
                };
                let ns = match self.peek().clone() {
                    Tok::Ident(ns) => {
                        self.bump();
                        ns
                    }
                    other => {
                        // Report the position of the namespace line, not the
                        // token on the following line.
                        return Err(ParseError {
                            msg: format!("期望命名空间标识符，实际是 `{other:?}`"),
                            line,
                            col,
                        });
                    }
                };
                if let Some(msg) = namespace_format_error(&ns) {
                    return Err(ParseError { msg, line, col });
                }
                if !matches!(self.peek(), Tok::Newline | Tok::Eof) {
                    return self.err(format!(
                        "`namespace {ns}` 之后必须是换行，实际是 `{:?}`",
                        self.peek()
                    ));
                }
                Ok(Item::Namespace(ns))
            }
            "sort" => {
                self.bump();
                let name = self.ident()?;
                let source = self.optional_source()?;
                Ok(Item::Sort { name, source })
            }
            "obj" | "object" | "individual" => {
                self.bump();
                let name = self.ident()?;
                self.expect(&Tok::Colon, "`:`")?;
                let ty = self.term()?;
                let source = self.optional_source()?;
                Ok(Item::Obj { name, ty, source })
            }
            "pred" => {
                self.bump();
                let name = self.ident()?;
                self.expect(&Tok::Colon, "`:`")?;
                let ty = self.term()?;
                let source = self.optional_source()?;
                Ok(Item::Pred { name, ty, source })
            }
            "axiom" => {
                self.bump();
                let name = self.ident()?;
                self.expect(&Tok::Colon, "`:`")?;
                let ty = self.term()?;
                // The clauses after the type are order-free: `source`,
                // `identity`, `occurred_at` and `occurred_in` may appear in any
                // order, each at most once. `effective` / `repealed` /
                // `jurisdiction` / `territory` are rule scope, not fact
                // metadata, and are refused below with a pointed message.
                let mut source: Option<SourceSpec> = None;
                let mut identity: Option<FactIdentity> = None;
                let mut occurred_at: Option<String> = None;
                let mut occurred_in: Option<String> = None;
                loop {
                    if let Some(next) = self.optional_source()? {
                        if source.is_some() {
                            return self.err(format!("`axiom {name}` 的 source 子句重复"));
                        }
                        source = Some(next);
                        continue;
                    }
                    if let Some(next) = self.optional_identity()? {
                        if identity.is_some() {
                            return self.err(format!(
                                "`axiom {name}` 的 identity 子句重复：一个事实只能有一个身份"
                            ));
                        }
                        identity = Some(next);
                        continue;
                    }
                    if let Some(next) = self.optional_occurrence("occurred_at")? {
                        if occurred_at.is_some() {
                            return self.err(format!(
                                "`axiom {name}` 的 occurred_at 子句重复：事实只能有一个发生日期"
                            ));
                        }
                        occurred_at = Some(next);
                        continue;
                    }
                    if let Some(next) = self.optional_occurrence("occurred_in")? {
                        if occurred_in.is_some() {
                            return self.err(format!(
                                "`axiom {name}` 的 occurred_in 子句重复：事实只能有一个发生地"
                            ));
                        }
                        occurred_in = Some(next);
                        continue;
                    }
                    break;
                }
                // A scope clause belongs to a rule. Leave it to the next item
                // when it starts a declaration; a clause that clearly tries to
                // annotate this fact is reported here.
                self.skip_newlines();
                if let Tok::Ident(keyword) = self.peek().clone() {
                    if matches!(
                        keyword.as_str(),
                        "effective" | "repealed" | "jurisdiction" | "territory"
                    ) {
                        return self.err(format!(
                            "`axiom {name}`：`{keyword}` 只能写在规则（rule）上；事实只能写 occurred_at / occurred_in"
                        ));
                    }
                }
                Ok(Item::Axiom {
                    name,
                    ty,
                    source,
                    identity,
                    occurred_at,
                    occurred_in,
                })
            }
            "def" => {
                // The definition is elaborated and kernel-checked after the
                // parse, so keep the declaration's own position: a bad body
                // must be reported at the source line that wrote it.
                let (line, col) = {
                    let token = self.here();
                    (token.line, token.col)
                };
                self.bump();
                let name = self.ident()?;
                self.expect(&Tok::Colon, "`:`")?;
                let ty = self.term()?;
                self.expect(&Tok::Assign, "`:=`")?;
                let body = self.term()?;
                let source = self.optional_source()?;
                Ok(Item::Def {
                    name,
                    ty,
                    body,
                    source,
                    line,
                    col,
                })
            }
            "rule" => {
                self.bump();
                let name = self.ident()?;
                self.rule_body(name)
            }
            "contrary" => {
                self.bump();
                let left = self.ident()?;
                let right = self.ident()?;
                let source = self.optional_source()?;
                Ok(Item::Contrary {
                    left,
                    right,
                    source,
                })
            }
            "unique" => {
                self.bump();
                let pred = self.ident()?;
                let raw = self.ident()?;
                let index: usize = match raw.parse() {
                    Ok(n) => n,
                    Err(_) => {
                        return self.err(format!("`unique {pred} {raw}`：参数位置必须是正整数"))
                    }
                };
                let source = self.optional_source()?;
                Ok(Item::Unique {
                    pred,
                    index,
                    source,
                })
            }
            "open" => {
                // The declaration's position is kept in the AST: the target is
                // validated against the completed environment (so a predicate
                // may be declared later in the same file), and those load
                // errors still have to point at the `open` line.
                let (line, col) = {
                    let token = self.here();
                    (token.line, token.col)
                };
                self.bump();
                let pred = match self.peek().clone() {
                    Tok::Ident(pred) => {
                        self.bump();
                        pred
                    }
                    other => {
                        return Err(ParseError {
                            msg: format!("`open` 之后必须是谓词名，实际是 `{other:?}`"),
                            line,
                            col,
                        });
                    }
                };
                if !matches!(self.peek(), Tok::Newline | Tok::Eof) {
                    let (bad_line, bad_col) = {
                        let token = self.here();
                        (token.line, token.col)
                    };
                    return Err(ParseError {
                        msg: format!("`open {pred}` 之后必须是换行，实际是 `{:?}`", self.peek()),
                        line: bad_line,
                        col: bad_col,
                    });
                }
                Ok(Item::Open { pred, line, col })
            }
            "priority" => {
                self.bump();
                let winner = self.ident()?;
                // `over` is a literal keyword of this declaration, not a
                // general identifier position. A missing one is reported at
                // the token that took its place.
                if !self.keyword("over") {
                    return self.err(format!(
                        "`priority {winner}` 缺少 `over`：应写成 `priority <胜者规则> over <败者规则> source …`，实际是 `{:?}`",
                        self.peek()
                    ));
                }
                self.bump();
                let loser = self.ident()?;
                // At least one usable source is required at load time, as for
                // a rule or an axiom; the parser only collects what is written.
                // Each `source` may be placed on the line after the `over`
                // clause, like `optional_source`; this is unambiguous because
                // `source` never starts a new item. The position is restored
                // when the next line starts something else, so the newline
                // before the next declaration is left to `program`.
                let mut sources = Vec::new();
                loop {
                    let save = self.pos;
                    self.skip_newlines_in_list();
                    if !self.keyword("source") {
                        self.pos = save;
                        break;
                    }
                    sources.push(self.source_spec()?);
                }
                Ok(Item::Priority {
                    winner,
                    loser,
                    sources,
                })
            }
            "interpret" | "interpretation" => self.interpretation(),
            "#check" | "check" => {
                self.bump();
                Ok(Item::Check(self.term()?))
            }
            "#why" | "why" => {
                self.bump();
                Ok(Item::Why(self.term()?))
            }
            "#gap" | "gap" => {
                self.bump();
                Ok(Item::Gap(self.term()?))
            }
            "#proposition" | "proposition" => {
                self.bump();
                Ok(Item::Proposition(self.term()?))
            }
            "#assert" | "assert" => self.err(ASSERT_RENAMED),
            "#show" | "show" => {
                self.bump();
                Ok(Item::Show(self.ident()?))
            }
            _ => self.err(format!("未知声明关键字 `{kw}`")),
        }
    }

    /// `interpret <id> : <from> → <to>`, then required `direction` and
    /// `source` clauses on their own lines.
    ///
    /// `from` and `to` are parsed at application level. This is what keeps the
    /// header on one line: a component that is itself an arrow must be
    /// parenthesized, and the clause keywords `direction` / `source` end the
    /// application instead of being swallowed as arguments.
    fn interpretation(&mut self) -> PResult<Item> {
        let (header_line, header_col) = {
            let token = self.here();
            (token.line, token.col)
        };
        self.bump();
        let name = self.ident()?;
        if !self.eat(&Tok::Colon) {
            return self.err(format!(
                "`interpret {name}` 缺少 `:`；应写成 `interpret {name} : <from> → <to>`，实际是 `{:?}`",
                self.peek()
            ));
        }
        let from = self
            .application_until_interpret_clause()
            .map_err(|error| ParseError {
                msg: format!("`interpret {name}` 的 from：{}", error.msg),
                line: error.line,
                col: error.col,
            })?;
        // A clause keyword after `from` is still on the header line; report it
        // as a line-placement error rather than as a missing arrow, so the
        // syntax stays line-oriented in both directions.
        if let Tok::Ident(clause) = self.peek().clone() {
            if (clause == "direction" || clause == "source") && self.here().line == header_line {
                return self.err_at(
                    header_line,
                    header_col,
                    format!(
                        "`interpret {name}` 的 `{clause}` 子句必须另起一行；\
                         头行只写 `interpret {name} : <from> → <to>`"
                    ),
                );
            }
        }
        if !self.eat(&Tok::Arrow) {
            return self.err(format!(
                "`interpret {name}` 的 from 之后缺少 `→`；应写成 `interpret {name} : <from> → <to>`，实际是 `{:?}`",
                self.peek()
            ));
        }
        let to = self
            .application_until_interpret_clause()
            .map_err(|error| ParseError {
                msg: format!("`interpret {name}` 的 to：{}", error.msg),
                line: error.line,
                col: error.col,
            })?;
        // `direction` and `source` are line-oriented clauses. Writing one on
        // the header line is refused here, before it can be mistaken for an
        // application argument.
        if let Tok::Ident(clause) = self.peek().clone() {
            if (clause == "direction" || clause == "source") && self.here().line == header_line {
                return self.err_at(
                    header_line,
                    header_col,
                    format!(
                        "`interpret {name}` 的 `{clause}` 子句必须另起一行；\
                         头行只写 `interpret {name} : <from> → <to>`"
                    ),
                );
            }
        }
        // A leftover arrow means a component was not parenthesized, e.g.
        // `interpret i : P → Q → R` — the `to` side ends at `Q`.
        if self.peek() == &Tok::Arrow {
            return self.err_at(
                header_line,
                header_col,
                format!(
                    "`interpret {name}` 的 from/to 只能是应用项：类型里的 `→` 必须用括号括起，例如 `(P → Q)`"
                ),
            );
        }

        let mut direction: Option<InterpretationDirection> = None;
        let mut sources: Vec<SourceSpec> = Vec::new();
        loop {
            let save = self.pos;
            self.skip_newlines();
            if matches!(self.peek(), Tok::Eof) {
                self.pos = save;
                break;
            }
            let Tok::Ident(keyword) = self.peek().clone() else {
                self.pos = save;
                break;
            };
            match keyword.as_str() {
                "direction" => {
                    let (line, col) = {
                        let token = self.here();
                        (token.line, token.col)
                    };
                    self.bump();
                    if direction.is_some() {
                        return self.err_at(
                            line,
                            col,
                            format!("`interpret {name}` 的 direction 子句重复：一个解释只能声明一个方向"),
                        );
                    }
                    let direction_keyword = match self.peek().clone() {
                        Tok::Ident(keyword) => {
                            self.bump();
                            keyword
                        }
                        other => {
                            return self.err_at(
                                line,
                                col,
                                format!(
                                    "`interpret {name}` 的 direction 缺少方向关键字；\
                                     可选：literal / expand / narrow / analogy，实际是 `{other:?}`"
                                ),
                            )
                        }
                    };
                    let Some(parsed) = InterpretationDirection::from_keyword(&direction_keyword)
                    else {
                        return self.err_at(
                            line,
                            col,
                            format!(
                                "`interpret {name}` 的未知方向 `{direction_keyword}`；\
                                 可选：literal / expand / narrow / analogy"
                            ),
                        );
                    };
                    direction = Some(parsed);
                    if !matches!(self.peek(), Tok::Newline | Tok::Eof) {
                        return self.err_at(
                            line,
                            col,
                            format!(
                                "`interpret {name}` 的 direction 子句之后必须是换行；\
                                 direction 与 source 必须各占一行"
                            ),
                        );
                    }
                }
                "source" => {
                    let (line, col) = {
                        let token = self.here();
                        (token.line, token.col)
                    };
                    // Every source error names the interpretation, so a
                    // missing text/locator is not just "a source clause".
                    let source = self.source_spec().map_err(|error| ParseError {
                        msg: format!("`interpret {name}` 的 source 子句：{}", error.msg),
                        line: error.line,
                        col: error.col,
                    })?;
                    for (field, value) in [
                        ("text", source.text.as_str()),
                        ("locator", source.locator.as_str()),
                        ("version", source.version.as_str()),
                    ] {
                        if value.trim().is_empty() {
                            return self.err_at(
                                line,
                                col,
                                format!(
                                    "`interpret {name}` 的 source 缺少非空的 `{field}`：\
                                     解释的出处必须写明文本、条号与版本"
                                ),
                            );
                        }
                    }
                    sources.push(source);
                    if !matches!(self.peek(), Tok::Newline | Tok::Eof) {
                        let next = match self.peek().clone() {
                            Tok::Ident(keyword) => keyword,
                            _ => String::new(),
                        };
                        let message = match next.as_str() {
                            "source" => format!(
                                "`interpret {name}` 的 `source` 子句必须另起一行：每个来源写一条 source"
                            ),
                            "direction" => format!(
                                "`interpret {name}` 的 `direction` 子句必须另起一行"
                            ),
                            _ => format!(
                                "`interpret {name}` 的 source 子句之后必须是换行，实际是 `{:?}`",
                                self.peek()
                            ),
                        };
                        return self.err_at(line, col, message);
                    }
                }
                other if is_item_keyword(other) => {
                    self.pos = save;
                    break;
                }
                other => {
                    return self.err_at(
                        header_line,
                        header_col,
                        format!(
                            "`interpret {name}` 里未知的子句 `{other}`；direction 与 source 必须各占一行"
                        ),
                    )
                }
            }
        }
        let Some(direction) = direction else {
            return self.err_at(
                header_line,
                header_col,
                format!(
                    "`interpret {name}` 缺少 direction 子句；\
                     必须另起一行写 `direction literal|expand|narrow|analogy`（没有默认方向）"
                ),
            );
        };
        if sources.is_empty() {
            return self.err_at(
                header_line,
                header_col,
                format!(
                    "`interpret {name}` 缺少 source 子句；解释必须至少有一条出处，\
                     另起一行写 `source text \"…\" locator \"…\" version \"…\"`"
                ),
            );
        }
        Ok(Item::Interpretation {
            name,
            from,
            to,
            direction,
            sources,
        })
    }

    fn rule_body(&mut self, name: String) -> PResult<Item> {
        // An optional `:` after the rule name makes the block read like a
        // heading; both forms are accepted.
        self.eat(&Tok::Colon);
        let mut params = Vec::new();
        let mut premises = Vec::new();
        let mut conclusion = None;
        let mut defeaters = Vec::new();
        let mut sources = Vec::new();
        let mut scope = ScopeSpec::default();
        // The pleading clauses are optional and each may appear at most once.
        // `None` here means "not declared": nothing fills in a default.
        let mut burden = None;
        let mut standard = None;
        let mut exception_burden = None;
        let mut exception_standard = None;

        loop {
            // Whether the next clause starts on a fresh line. Scope clauses
            // require it, like `identity`: a clause crammed onto the previous
            // line is refused instead of silently accepted.
            let save = self.pos;
            self.skip_newlines();
            let on_new_line = self.pos > save;
            if matches!(self.peek(), Tok::Eof) {
                break;
            }
            let Tok::Ident(kw) = self.peek().clone() else {
                break;
            };
            match kw.as_str() {
                "params" => {
                    self.bump();
                    loop {
                        self.skip_newlines_in_list();
                        let n = self.ident()?;
                        self.expect(&Tok::Colon, "`:`")?;
                        let t = self.term()?;
                        params.push((n, t));
                        if params.len() + premises.len() > MAX_RULE_BINDERS {
                            return self.err(format!(
                                "规则 `{name}` 的参数与前提合计超过上限 {MAX_RULE_BINDERS}"
                            ));
                        }
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        self.skip_newlines_in_list();
                    }
                }
                "premise" | "premises" | "pre" => {
                    self.bump();
                    // Three accepted spellings:
                    //   premise <term>
                    //   premise p : <term>
                    //   premise p : <term>   (the name is then usable later)
                    let named =
                        matches!(self.peek(), Tok::Ident(_)) && self.peek_at(1) == &Tok::Colon;
                    let nm = if named {
                        let n = self.ident()?;
                        self.bump(); // ':'
                        Some(n)
                    } else {
                        None
                    };
                    let t = self.term()?;
                    premises.push(Premise { name: nm, ty: t });
                    if params.len() + premises.len() > MAX_RULE_BINDERS {
                        return self.err(format!(
                            "规则 `{name}` 的参数与前提合计超过上限 {MAX_RULE_BINDERS}"
                        ));
                    }
                }
                "conclude" | "conclusion" => {
                    self.bump();
                    conclusion = Some(self.term()?);
                }
                "unless" => {
                    self.bump();
                    defeaters.push(Defeater::Unless(self.term()?));
                }
                "defeated_by" | "defeated" => {
                    self.bump();
                    defeaters.push(Defeater::By(self.ident()?));
                }
                "prefer" => {
                    self.bump();
                    defeaters.push(Defeater::Prefer(self.ident()?));
                }
                "burden" => {
                    let (line, col) = (self.here().line, self.here().col);
                    self.bump();
                    if burden.is_some() {
                        return Err(duplicate_clause(&name, "burden", line, col));
                    }
                    burden = Some(self.burden_value(&name, "burden")?);
                }
                "standard" => {
                    let (line, col) = (self.here().line, self.here().col);
                    self.bump();
                    if standard.is_some() {
                        return Err(duplicate_clause(&name, "standard", line, col));
                    }
                    standard = Some(self.standard_value(&name, "standard")?);
                }
                "exception_burden" => {
                    let (line, col) = (self.here().line, self.here().col);
                    self.bump();
                    if exception_burden.is_some() {
                        return Err(duplicate_clause(&name, "exception_burden", line, col));
                    }
                    exception_burden = Some(self.burden_value(&name, "exception_burden")?);
                }
                "exception_standard" => {
                    let (line, col) = (self.here().line, self.here().col);
                    self.bump();
                    if exception_standard.is_some() {
                        return Err(duplicate_clause(&name, "exception_standard", line, col));
                    }
                    exception_standard = Some(self.standard_value(&name, "exception_standard")?);
                }
                "source" => {
                    // A source clause inside a rule body names the rule in its
                    // diagnostics, so a malformed quote or a misplaced scope
                    // keyword points at which rule must be fixed.
                    let spec = self.source_spec().map_err(|mut error| {
                        error.msg = format!("`rule {name}` 的 source 子句：{}", error.msg);
                        error
                    })?;
                    sources.push(spec);
                }
                // Scope clauses are metadata on the rule, one clause per line.
                // The values are validated when the theory is loaded; the
                // parser only refuses duplicates and wrong clause kinds.
                "effective" => {
                    self.require_clause_new_line(&name, "effective", on_new_line)?;
                    self.scope_clause(&name, "effective", &mut scope.effective_from)?;
                }
                "repealed" => {
                    self.require_clause_new_line(&name, "repealed", on_new_line)?;
                    self.scope_clause(&name, "repealed", &mut scope.effective_to)?;
                }
                "jurisdiction" => {
                    self.require_clause_new_line(&name, "jurisdiction", on_new_line)?;
                    self.scope_clause(&name, "jurisdiction", &mut scope.jurisdiction)?;
                }
                "territory" => {
                    self.require_clause_new_line(&name, "territory", on_new_line)?;
                    self.scope_clause(&name, "territory", &mut scope.territory)?;
                }
                "occurred_at" | "occurred_in" => {
                    return self.err(format!(
                        "`rule {name}` 的 `{kw}`：它只能写在事实（axiom 命题）上；规则不能声明发生时间或发生地"
                    ));
                }
                // Another item starts here. `#` covers every sigiled command:
                // the lexer splits the sigil from the command name, so the
                // combined spellings never reach this match.
                other if is_item_keyword(other) => break,
                other => return self.err(format!("规则 `{name}` 里未知的子句 `{other}`")),
            }
        }

        let Some(conclusion) = conclusion else {
            return self.err(format!("规则 `{name}` 缺少 conclude 子句"));
        };
        Ok(Item::Rule {
            name,
            params,
            premises,
            conclusion,
            defeaters,
            sources,
            scope,
            burden,
            standard,
            exception_burden,
            exception_standard,
        })
    }

    /// Refuse a rule scope clause that does not start its own line.
    ///
    /// Every new clause is line-oriented: `effective 1999-10-01 repealed
    /// 2021-01-01` on one line is refused rather than read as a clause plus a
    /// stray token. Ordinary identifiers after a scope value are still left to
    /// the regular unknown-clause diagnostic.
    fn require_clause_new_line(&self, rule: &str, keyword: &str, on_new_line: bool) -> PResult<()> {
        if on_new_line {
            return Ok(());
        }
        self.err(format!(
            "`rule {rule}` 的 `{keyword}` 子句必须另起一行；每个作用域子句独占一行"
        ))
    }

    /// Parse the value of one scope clause and store it, refusing a repeat.
    ///
    /// The value is a bare token; dates and codes are checked by the loader so
    /// a malformed date and a malformed `--as-of` share one error message. The
    /// messages name the rule: the loader's errors do too, so both stages point
    /// at the declaration that must be fixed.
    fn scope_clause(
        &mut self,
        rule: &str,
        keyword: &str,
        slot: &mut Option<String>,
    ) -> PResult<()> {
        let (line, col) = {
            let token = self.here();
            (token.line, token.col)
        };
        self.bump(); // the keyword
        let value = match self.peek().clone() {
            Tok::Ident(value) => {
                self.bump();
                value
            }
            Tok::Newline | Tok::Eof => {
                return Err(ParseError {
                    msg: format!(
                        "`rule {rule}` 的 `{keyword}` 缺少值（用法：`{keyword} <日期或代码>`）"
                    ),
                    line,
                    col,
                })
            }
            other => {
                return Err(ParseError {
                    msg: format!(
                        "`rule {rule}` 的 `{keyword}` 之后必须是裸值（日期或代码），\
                         实际是 `{other:?}`；不要写成字符串字面量"
                    ),
                    line,
                    col,
                })
            }
        };
        if slot.replace(value).is_some() {
            return Err(ParseError {
                msg: format!("`rule {rule}` 的 `{keyword}` 子句重复：一个作用域字段只能写一次"),
                line,
                col,
            });
        }
        Ok(())
    }

    /// The written value of a `burden` / `exception_burden` clause together
    /// with its position. A value must follow on the same line; a clause whose
    /// value is missing is an error, not an omitted declaration.
    fn burden_value(&mut self, rule: &str, field: &str) -> PResult<Burden> {
        let (written, line, col) = self.clause_value(rule, field, Burden::labels())?;
        match Burden::parse(&written) {
            Some(value) => Ok(value),
            None => Err(ParseError {
                msg: format!(
                    "规则 `{rule}` 的 {field} 取值 `{written}` 非法；允许的取值：{}",
                    Burden::labels().join("、")
                ),
                line,
                col,
            }),
        }
    }

    /// The written value of a `standard` / `exception_standard` clause.
    fn standard_value(&mut self, rule: &str, field: &str) -> PResult<Standard> {
        let (written, line, col) = self.clause_value(rule, field, Standard::labels())?;
        match Standard::parse(&written) {
            Some(value) => Ok(value),
            None => Err(ParseError {
                msg: format!(
                    "规则 `{rule}` 的 {field} 取值 `{written}` 非法；允许的取值：{}",
                    Standard::labels().join("、")
                ),
                line,
                col,
            }),
        }
    }

    /// Read one keyword value for a rule clause, or report that it is missing
    /// together with the allowed set. The value must be on the clause's own
    /// line: a newline here means the author forgot it.
    fn clause_value(
        &mut self,
        rule: &str,
        field: &str,
        allowed: &[&str],
    ) -> PResult<(String, usize, usize)> {
        let (line, col) = (self.here().line, self.here().col);
        if let Tok::Ident(written) = self.peek().clone() {
            self.bump();
            Ok((written, line, col))
        } else {
            Err(ParseError {
                msg: format!(
                    "规则 `{rule}` 的 {field} 缺少取值；允许的取值：{}",
                    allowed.join("、")
                ),
                line,
                col,
            })
        }
    }

    fn skip_newlines_in_list(&mut self) {
        // A newline after a comma inside `params` is harmless; consume it.
        while matches!(self.peek(), Tok::Newline) {
            self.bump();
        }
    }

    fn optional_source(&mut self) -> PResult<Option<SourceSpec>> {
        // A `source` clause may be placed on the line after its declaration.
        // This is unambiguous because `source` never starts a new item.
        let save = self.pos;
        self.skip_newlines_in_list();
        if self.keyword("source") {
            Ok(Some(self.source_spec()?))
        } else {
            self.pos = save;
            Ok(None)
        }
    }

    /// Parse an optional `identity <keyword>` clause.
    ///
    /// The clause must start its own line. `identity` is also an ordinary
    /// identifier, so the clause is recognised only when the next token is
    /// one of the five identity keywords; otherwise the position is restored
    /// and the line is left to the next declaration. A declaration-shaped
    /// line (`identity 定义 : ...`) is left alone the same way, so it is
    /// reported at its own position instead of being swallowed into this
    /// declaration. A line that clearly attempts the clause
    /// (`identity verifiedd`) reports the unknown keyword here.
    fn optional_identity(&mut self) -> PResult<Option<FactIdentity>> {
        let save = self.pos;
        self.skip_newlines_in_list();
        let on_new_line = self.pos > save;
        if !self.keyword("identity") {
            self.pos = save;
            return Ok(None);
        }
        let (line, col) = {
            let token = self.here();
            (token.line, token.col)
        };
        // A type line is protected by `application()`: an `identity` written
        // there is parsed as an argument. A `source` clause is not, so the
        // clause after it must be told to start a fresh line explicitly.
        if !on_new_line {
            return Err(ParseError {
                msg: "`identity` 子句必须另起一行".into(),
                line,
                col,
            });
        }
        match self.peek_at(1).clone() {
            Tok::Ident(keyword) => {
                if let Some(identity) = FactIdentity::from_keyword(&keyword) {
                    self.bump(); // `identity`
                    self.bump(); // the keyword
                    return Ok(Some(identity));
                }
                // `identity <name> : ...` is shaped like a new declaration,
                // not like an identity clause. Leave it to the item parser.
                if self.peek_at(2) == &Tok::Colon {
                    self.pos = save;
                    return Ok(None);
                }
                Err(ParseError {
                    msg: format!(
                        "未知事实身份 `{keyword}`；可选：verified / user_asserted / assumed / disputed / stipulated"
                    ),
                    line,
                    col,
                })
            }
            _ => Err(ParseError {
                msg: "`identity` 之后缺少事实身份关键字；可选：verified / user_asserted / assumed / disputed / stipulated".into(),
                line,
                col,
            }),
        }
    }

    /// Parse an optional `occurred_at <date>` / `occurred_in <code>` clause.
    ///
    /// Like `identity`, the clause must start its own line: the fact's type
    /// would otherwise swallow the keyword as an application argument. The
    /// value is a bare token (a date or a jurisdiction code), validated when
    /// the theory is loaded. The position is restored when the keyword is not
    /// present, so the caller can try the other clauses and the next item.
    fn optional_occurrence(&mut self, keyword: &str) -> PResult<Option<String>> {
        let save = self.pos;
        self.skip_newlines_in_list();
        let on_new_line = self.pos > save;
        if !self.keyword(keyword) {
            self.pos = save;
            return Ok(None);
        }
        let (line, col) = {
            let token = self.here();
            (token.line, token.col)
        };
        if !on_new_line {
            return Err(ParseError {
                msg: format!("`{keyword}` 子句必须另起一行"),
                line,
                col,
            });
        }
        self.bump(); // the keyword
        match self.peek().clone() {
            Tok::Ident(value) => {
                self.bump();
                Ok(Some(value))
            }
            other => Err(ParseError {
                msg: format!(
                    "`{keyword}` 之后必须是裸值（日期或代码），实际是 `{other:?}`；\
                     不要写成字符串字面量"
                ),
                line,
                col,
            }),
        }
    }

    /// `source text "宪法" locator "第三十九条" version "2018"`
    ///
    /// Fields may be separated by newlines. The clause ends before the first
    /// token that is not one of the known keys; that token is left for the
    /// caller. `text` and `locator` must be present and non-empty.
    fn source_spec(&mut self) -> PResult<SourceSpec> {
        self.bump(); // 'source'
        let mut s = SourceSpec::default();
        let mut seen: Vec<String> = Vec::new();
        let mut first = true;
        loop {
            // A newline belongs to the source clause only when a known key
            // follows it. Otherwise restore it so the caller decides.
            let save = self.pos;
            self.skip_newlines();
            let key = match self.peek().clone() {
                Tok::Ident(key) if is_source_key(&key) => key,
                other => {
                    if first {
                        return self.err(format!(
                            "source 子句期望已知键（text、locator 等），实际是 `{other:?}`"
                        ));
                    }
                    self.pos = save;
                    break;
                }
            };
            let (key_line, key_col) = {
                let key_token = self.here();
                (key_token.line, key_token.col)
            };
            // `effective`, `jurisdiction` and `territory` are also rule scope
            // clause keywords. A scope clause writes a bare value on its own
            // line, while a source field always writes a quoted string; so a
            // key that starts a new line but is not followed by a string ends
            // the source clause and is left for the rule body. On the same
            // line the old source-field rule still applies, so a missing quote
            // is still an error instead of a silently different clause.
            let starts_new_line = self.pos > save;
            if !first
                && starts_new_line
                && is_scope_clause_key(&key)
                && !matches!(self.peek_at(1), Tok::Str(_))
            {
                self.pos = save;
                break;
            }
            self.bump();
            if seen.contains(&key) {
                return Err(ParseError {
                    msg: format!("source 子句的键 `{key}` 重复"),
                    line: key_line,
                    col: key_col,
                });
            }
            seen.push(key.clone());
            let value = match self.peek().clone() {
                Tok::Str(value) => {
                    self.bump();
                    value
                }
                // `effective`, `jurisdiction` and `territory` are also rule
                // scope clause keywords with bare values. Reaching this branch
                // means a scope clause was misplaced inside a source (same
                // line, or before any source field); say so instead of
                // claiming a source value must be quoted.
                other if is_scope_clause_key(&key) => {
                    return Err(ParseError {
                        msg: format!(
                            "`source` 的键 `{key}` 需要双引号字符串；\
                             规则作用域子句 `{key} <日期或代码>` 必须单独占一行，写在 source 子句之外\
                             （实际是 `{other:?}`）"
                        ),
                        line: key_line,
                        col: key_col,
                    })
                }
                other => {
                    return self.err(format!(
                        "键 `{key}` 的值必须是双引号字符串字面量，实际是 `{other:?}`"
                    ))
                }
            };
            match key.as_str() {
                "text" => s.text = value,
                "locator" => s.locator = value,
                "version" => s.version = value,
                "effective" => s.effective = Some(value),
                "quote" => s.quote = value,
                "url" => s.url = value,
                "jurisdiction" => s.jurisdiction = value,
                "retrieved_at" => s.retrieved_at = value,
                "hash" => s.hash = value,
                "note" => s.note = value,
                _ => unreachable!("is_source_key accepts only the keys above"),
            }
            first = false;
        }
        if s.text.is_empty() {
            return self.err("source 子句缺少非空的 `text`");
        }
        if s.locator.is_empty() {
            return self.err("source 子句缺少非空的 `locator`");
        }
        Ok(s)
    }

    // ---------------- terms ----------------

    pub fn term(&mut self) -> PResult<Term> {
        if self.depth >= MAX_TERM_DEPTH {
            return Err(ParseError {
                msg: format!("项嵌套深度超过上限 {MAX_TERM_DEPTH}（括号、→、∀ 或 λ 套得太深）"),
                line: self.here().line,
                col: self.here().col,
            });
        }
        self.depth += 1;
        let result = self.term_inner();
        self.depth -= 1;
        result
    }

    fn term_inner(&mut self) -> PResult<Term> {
        // A leading `#` is a command sigil, tolerated here so that a bare
        // term can be handed to the parser in either form.
        if self.peek() == &Tok::Ident("#".into()) {
            self.bump();
        }
        // A term may begin on the line after its keyword; that is what makes
        // `def f : T :=\n  λ ...` read like Lean.
        self.skip_newlines_in_list();
        self.arrow()
    }

    fn arrow(&mut self) -> PResult<Term> {
        let dom = self.application()?;
        if self.eat(&Tok::Arrow) {
            // An arrow is an explicit continuation: allow the codomain to
            // start on the next line, as in Lean.
            self.skip_newlines_in_list();
            let cod = self.term()?;
            return Ok(Term::Pi {
                name: None,
                domain: Box::new(dom),
                codomain: Box::new(cod),
            });
        }
        Ok(dom)
    }

    fn application(&mut self) -> PResult<Term> {
        let mut t = self.atom()?;
        let mut arguments = 0usize;
        while let Tok::Ident(_) | Tok::LParen = self.peek() {
            arguments += 1;
            if arguments > MAX_APPLICATION_ARITY {
                return self.err(format!("应用的参数数量超过上限 {MAX_APPLICATION_ARITY}"));
            }
            let a = self.atom()?;
            t = Term::App(Box::new(t), Box::new(a));
        }
        Ok(t)
    }

    /// Application parsing for an interpretation's `to` side.
    ///
    /// `direction` and `source` are reserved clause keywords there: stopping
    /// before them lets the caller report "must start its own line" instead of
    /// silently turning the clause into an application argument.
    fn application_until_interpret_clause(&mut self) -> PResult<Term> {
        let mut t = self.atom()?;
        loop {
            match self.peek() {
                Tok::LParen => {}
                Tok::Ident(next) if next == "direction" || next == "source" => break,
                Tok::Ident(_) => {}
                _ => break,
            }
            let a = self.atom()?;
            t = Term::App(Box::new(t), Box::new(a));
        }
        Ok(t)
    }

    fn atom(&mut self) -> PResult<Term> {
        if self.peek() == &Tok::Ident("#".into()) {
            // `#check foo` used as a command wrapper: consume the sigil.
            self.bump();
        }
        match self.peek().clone() {
            Tok::LParen => {
                self.bump();
                let t = self.term()?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(t)
            }
            Tok::Forall => {
                self.bump();
                let (n, d) = self.binder()?;
                self.expect(&Tok::Comma, "`,`")?;
                let body = self.term()?;
                Ok(Term::Pi {
                    name: Some(n),
                    domain: Box::new(d),
                    codomain: Box::new(body),
                })
            }
            Tok::Lambda => {
                self.bump();
                let (n, d) = self.binder()?;
                self.expect(&Tok::Assign, "`:=` 或 `=>`")?;
                // A lambda body may start on the next line.
                self.skip_newlines_in_list();
                let body = self.term()?;
                Ok(Term::Lam {
                    name: n,
                    domain: Box::new(d),
                    body: Box::new(body),
                })
            }
            Tok::Ident(s) => {
                self.bump();
                match s.as_str() {
                    "Prop" => Ok(Term::Prop),
                    "Type" => {
                        // `Type n`: look ahead for a numeral identifier.
                        if let Tok::Ident(n) = self.peek().clone() {
                            if n.chars().all(|c| c.is_ascii_digit()) {
                                self.bump();
                                return Ok(Term::Type(Some(n.parse().unwrap_or(0))));
                            }
                        }
                        Ok(Term::Type(None))
                    }
                    _ => Ok(Term::Ident(s)),
                }
            }
            Tok::Underscore => {
                self.bump();
                Ok(Term::Ident("_".into()))
            }
            other => self.err(format!("期望项，实际是 `{other:?}`")),
        }
    }

    /// `(x : A)` or a bare `x`.
    fn binder(&mut self) -> PResult<(String, Term)> {
        if self.eat(&Tok::LParen) {
            let n = self.ident()?;
            self.expect(&Tok::Colon, "`:`")?;
            let t = self.term()?;
            self.expect(&Tok::RParen, "`)`")?;
            Ok((n, t))
        } else {
            let n = self.ident()?;
            self.err::<(String, Term)>(format!("绑定 `{n}` 缺少类型，请写成 `({n} : T)`"))
        }
    }
}

/// Whether a keyword starts a top-level declaration or command. Used to end a
/// clause block without swallowing the next item.
fn is_item_keyword(keyword: &str) -> bool {
    matches!(
        keyword,
        "#" | "import"
            | "namespace"
            | "rule"
            | "sort"
            | "pred"
            | "axiom"
            | "def"
            | "interpret"
            | "interpretation"
            | "contrary"
            | "unique"
            | "open"
            | "priority"
            | "obj"
            | "object"
            | "individual"
            | "check"
            | "why"
            | "gap"
            | "proposition"
            | "assert"
            | "show"
    )
}

/// A repeated rule clause is an error: the second declaration would silently
/// override or duplicate the first, so the file would be ambiguous. The
/// position points at the repeated clause's keyword.
fn duplicate_clause(rule: &str, field: &str, line: usize, col: usize) -> ParseError {
    ParseError {
        msg: format!("规则 `{rule}` 的 {field} 重复声明；同一子句只能出现一次"),
        line,
        col,
    }
}

/// Parse a whole program.
pub fn parse(src: &str) -> PResult<Vec<Item>> {
    let toks = crate::lexer::lex(src).map_err(|e| ParseError {
        msg: e.msg,
        line: e.line,
        col: e.col,
    })?;
    let mut p = Parser::new(toks);
    p.program()
}
