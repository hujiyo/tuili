//! Recursive-descent parser for Lean-style surface syntax.
//!
//! Grammar (summary):
//!
//! ```text
//! program  := namespace? item*
//! namespace := 'namespace' NAMESPACE      (first item only)
//! item     := sort | pred | axiom | def | rule | interpret | contrary | unique | command
//! sort     := 'sort' IDENT source?
//! pred     := 'pred' IDENT ':' term source?
//! axiom    := 'axiom' IDENT ':' term source?
//! def      := 'def' IDENT ':' term ':=' term source?
//! rule     := 'rule' IDENT clause+
//! clause   := 'params' binder (',' binder)*
//!           | 'premise' (binder ':')? term
//!           | 'conclude' term
//!           | 'unless' term
//!           | 'defeated_by' IDENT
//!           | 'prefer' IDENT
//!           | 'source' (source_key STRING)+
//! source_key := 'text' | 'locator' | 'version' | 'effective' | 'quote' | 'url'
//!           | 'jurisdiction' | 'retrieved_at' | 'hash' | 'note'
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

use crate::ast::*;
use crate::lexer::{Tok, Token};

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
}

pub type PResult<T> = Result<T, ParseError>;

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
        Parser { toks, pos: 0 }
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
            if self.keyword("namespace") {
                if namespace_seen {
                    return self.err("namespace 只能出现一次");
                }
                if !items.is_empty() {
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
                let source = self.optional_source()?;
                Ok(Item::Axiom { name, ty, source })
            }
            "def" => {
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
            "interpret" | "interpretation" => {
                self.bump();
                let name = self.ident()?;
                self.expect(&Tok::Colon, "`:`")?;
                // `term` consumes a top-level `→` itself, so the source side
                // is parsed at application level; a source-side function
                // type needs parentheses. The target side may be any term.
                let from = self.application()?;
                self.expect(&Tok::Arrow, "`→`")?;
                let to = self.term()?;
                let mut sources = Vec::new();
                while self.keyword("source") {
                    sources.push(self.source_spec()?);
                }
                Ok(Item::Interpretation {
                    name,
                    from,
                    to,
                    sources,
                })
            }
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

    fn rule_body(&mut self, name: String) -> PResult<Item> {
        // An optional `:` after the rule name makes the block read like a
        // heading; both forms are accepted.
        self.eat(&Tok::Colon);
        let mut params = Vec::new();
        let mut premises = Vec::new();
        let mut conclusion = None;
        let mut defeaters = Vec::new();
        let mut sources = Vec::new();

        loop {
            self.skip_newlines();
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
                "source" => {
                    sources.push(self.source_spec()?);
                }
                // Another item starts here. `#` covers every sigiled command:
                // the lexer splits the sigil from the command name, so the
                // combined spellings never reach this match.
                "#" | "namespace" | "rule" | "sort" | "pred" | "axiom" | "def" | "interpret"
                | "interpretation" | "contrary" | "unique" | "obj" | "object" | "individual"
                | "check" | "why" | "gap" | "proposition" | "assert" | "show" => break,
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
        })
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
        while let Tok::Ident(_) | Tok::LParen = self.peek() {
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
