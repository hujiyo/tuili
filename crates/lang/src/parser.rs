//! Recursive-descent parser for Lean-style surface syntax.
//!
//! Grammar (summary):
//!
//! ```text
//! program  := item*
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
//!           | 'source' STRING (STRING ('(' IDENT ')')?)?
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
        loop {
            self.skip_newlines();
            if matches!(self.peek(), Tok::Eof) {
                break;
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
            "check" | "why" | "gap" | "assert" | "show" if already_bumped => {
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
            "assert" => Ok(Item::Assert(self.term()?)),
            "show" => Ok(Item::Show(self.ident()?)),
            other => self.err(format!("未知命令 `#{other}`")),
        }
    }

    /// Dispatch an un-sigiled keyword. This is the bulk of `item`, split out
    /// so the `#`-command path above stays short.
    fn dispatch_plain(&mut self, kw: &str) -> PResult<Item> {
        match kw {
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
                let from = self.term()?;
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
            "#assert" | "assert" => {
                self.bump();
                Ok(Item::Assert(self.term()?))
            }
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
                // Another item starts here.
                "rule" | "sort" | "pred" | "axiom" | "def" | "interpret" | "interpretation"
                | "contrary" | "unique" | "obj" | "object" | "individual" | "#check" | "#why"
                | "#gap" | "#assert" | "#show" => break,
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

    /// `source "宪法" "第三十九条" (version "2018") (effective "1982")`
    fn source_spec(&mut self) -> PResult<SourceSpec> {
        self.bump(); // 'source'
        let mut s = SourceSpec::default();
        // At least one string-like token: identifiers or quoted chunks are
        // not distinguished; take everything up to a newline or a clause
        // keyword.
        let mut parts = Vec::new();
        loop {
            match self.peek().clone() {
                Tok::Ident(_) if !self.is_clause_keyword() => {
                    let t = self.ident()?;
                    parts.push(t);
                }
                Tok::LParen => {
                    // `(version "2018")`
                    self.bump();
                    let k = self.ident()?;
                    let v = self.ident()?;
                    self.expect(&Tok::RParen, "`)`")?;
                    match k.as_str() {
                        "version" => s.version = v,
                        "effective" => s.effective = Some(v),
                        "note" => s.note = v,
                        _ => {}
                    }
                }
                _ => break,
            }
        }
        if let Some(first) = parts.first() {
            s.text = first.clone();
        }
        // The rest of the parts concatenate into the locator, which may be
        // split across tokens such as `第十三` `条`.
        s.locator = parts.into_iter().skip(1).collect::<Vec<_>>().join("");
        if s.locator.is_empty() && !s.text.is_empty() {
            // `source 第三十九条` — treat the single part as the locator and
            // leave the text blank; the caller may fill it in from a module.
            s.locator = std::mem::take(&mut s.text);
        }
        Ok(s)
    }

    fn is_clause_keyword(&self) -> bool {
        matches!(self.peek(), Tok::Ident(s) if matches!(s.as_str(),
            "params" | "premise" | "premises" | "pre" | "conclude" | "conclusion"
            | "unless" | "defeated_by" | "defeated" | "prefer" | "source"
            | "rule" | "sort" | "pred" | "axiom" | "def" | "interpret"
            | "interpretation" | "contrary" | "unique" | "obj" | "object" | "individual"
            | "#check" | "#why" | "#gap" | "#assert" | "#show"))
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
        loop {
            match self.peek() {
                Tok::Ident(_) | Tok::LParen => {
                    let a = self.atom()?;
                    t = Term::App(Box::new(t), Box::new(a));
                }
                _ => break,
            }
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
            self.err::<(String, Term)>(format!(
                "绑定 `{n}` 缺少类型，请写成 `({n} : T)`"
            ))
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
