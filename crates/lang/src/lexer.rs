//! Lexer. The surface syntax uses Lean-style keywords and Unicode, but the
//! operator set is deliberately tiny so that a reader can hold it in their
//! head. Identifiers may contain `.` and `-` inside them, so a qualified name
//! such as `cn.constitution.公民` is one token; `->` and `--` keep their
//! operator/comment precedence.

use std::fmt;

use std_deduce_kernel::env::escape_control;

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    /// A bare identifier or keyword. `(`/`)` etc. are their own tokens.
    Ident(String),
    /// A double-quoted string literal. Values in a `source` clause use it;
    /// escapes are limited to `\\`, `\"`, `\n`, `\t` and `\r`.
    Str(String),
    /// →, in, forall, Pi, lambda are all lowered to `Tok::Ident` keywords so
    /// the parser does not care whether a user types "->" or "→".
    Arrow,
    Colon,
    Comma,
    LParen,
    RParen,
    LBrace,
    RBrace,
    /// `:=`
    Assign,
    /// `:=` used as a definition separator is the same token; a distinct
    /// token exists for `:` in lexical rendering of declarations.
    Eq,
    /// `∀`
    Forall,
    /// `λ`
    Lambda,
    /// `_` wildcard.
    Underscore,
    Newline,
    Eof,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tok: Tok,
    pub line: usize,
    pub col: usize,
}

/// The longest identifier (in characters) the lexer will produce.
///
/// Identifiers are copied into every token, every declaration and every
/// diagnostic. A file is untrusted input, so a multi-megabyte "name" must fail
/// with a locatable error instead of being carried through the whole pipeline.
/// The bound is far above any real legal term or namespace.
pub const MAX_IDENTIFIER_CHARS: usize = 1024;

/// Lex a whole program into tokens, discarding whitespace and comments
/// but keeping newlines (the grammar is line-oriented at the command level).
pub fn lex(src: &str) -> Result<Vec<Token>, LexError> {
    let mut out = Vec::new();
    let bytes: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut line = 1;
    let mut col = 1;

    while i < bytes.len() {
        let ch = bytes[i];
        match ch {
            ' ' | '\t' | '\r' => {
                i += 1;
                col += 1;
            }
            '\n' => {
                out.push(Token {
                    tok: Tok::Newline,
                    line,
                    col,
                });
                i += 1;
                line += 1;
                col = 1;
            }
            '-' if i + 1 < bytes.len() && (bytes[i + 1] == '-' || bytes[i + 1] == '>') => {
                if bytes[i + 1] == '>' {
                    out.push(Token {
                        tok: Tok::Arrow,
                        line,
                        col,
                    });
                    i += 2;
                    col += 2;
                } else {
                    // Line comment: skip to end of line.
                    while i < bytes.len() && bytes[i] != '\n' {
                        i += 1;
                    }
                }
            }
            '→' => {
                out.push(Token {
                    tok: Tok::Arrow,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            ':' if i + 1 < bytes.len() && bytes[i + 1] == '=' => {
                out.push(Token {
                    tok: Tok::Assign,
                    line,
                    col,
                });
                i += 2;
                col += 2;
            }
            ':' => {
                out.push(Token {
                    tok: Tok::Colon,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            ',' => {
                out.push(Token {
                    tok: Tok::Comma,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            '(' => {
                out.push(Token {
                    tok: Tok::LParen,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            ')' => {
                out.push(Token {
                    tok: Tok::RParen,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            '{' => {
                out.push(Token {
                    tok: Tok::LBrace,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            '}' => {
                out.push(Token {
                    tok: Tok::RBrace,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            '∀' => {
                out.push(Token {
                    tok: Tok::Forall,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            'λ' => {
                out.push(Token {
                    tok: Tok::Lambda,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            '=' => {
                out.push(Token {
                    tok: Tok::Eq,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            '"' => {
                let start_line = line;
                let start_col = col;
                i += 1;
                col += 1;
                let mut value = String::new();
                loop {
                    if i >= bytes.len() {
                        return Err(LexError {
                            msg: "未闭合字符串".into(),
                            line: start_line,
                            col: start_col,
                        });
                    }
                    match bytes[i] {
                        '"' => {
                            i += 1;
                            col += 1;
                            break;
                        }
                        '\\' => {
                            let escape_line = line;
                            let escape_col = col;
                            i += 1;
                            col += 1;
                            if i >= bytes.len() {
                                return Err(LexError {
                                    msg: "未闭合字符串".into(),
                                    line: start_line,
                                    col: start_col,
                                });
                            }
                            match bytes[i] {
                                '\\' => value.push('\\'),
                                '"' => value.push('"'),
                                'n' => value.push('\n'),
                                't' => value.push('\t'),
                                'r' => value.push('\r'),
                                '\n' | '\r' => {
                                    return Err(LexError {
                                        msg: "字符串字面量内不能出现裸换行；请写 `\\n`".into(),
                                        line,
                                        col,
                                    })
                                }
                                other => {
                                    return Err(LexError {
                                        msg: format!("未知转义序列 `\\{other}`"),
                                        line: escape_line,
                                        col: escape_col,
                                    })
                                }
                            }
                            i += 1;
                            col += 1;
                        }
                        '\n' | '\r' => {
                            return Err(LexError {
                                msg: "字符串字面量内不能出现裸换行；请写 `\\n`".into(),
                                line,
                                col,
                            })
                        }
                        c if c.is_control() => {
                            return Err(LexError {
                                msg: "字符串字面量内不能出现裸控制字符；请写 `\\t` 等转义".into(),
                                line,
                                col,
                            })
                        }
                        c => {
                            value.push(c);
                            i += 1;
                            col += 1;
                        }
                    }
                }
                out.push(Token {
                    tok: Tok::Str(value),
                    line: start_line,
                    col: start_col,
                });
            }
            '—' | '─' | '\'' => {
                // An em dash or single quote starts a comment-ish delimiter
                // that skips to the next newline, so prose punctuation never
                // derails lexing. Double quotes are string delimiters above.
                while i < bytes.len() && bytes[i] != '\n' {
                    i += 1;
                }
            }
            '#' => {
                // Command sigil: the *name* after it is the keyword.
                out.push(Token {
                    tok: Tok::Ident("#".into()),
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            c if c.is_alphanumeric() || c == '_' || is_cjk(c) || c == '\u{0027}' => {
                let start = i;
                let start_line = line;
                let start_col = col;
                while i < bytes.len() {
                    let d = bytes[i];
                    let continues = d.is_alphanumeric()
                        || d == '_'
                        || is_cjk(d)
                        || d == '\u{0027}'
                        || d == '·'
                        || d == '′'
                        || d == '.'
                        // A `-` belongs to an identifier only when it is not
                        // the start of a comment (`--`) or an arrow (`->`);
                        // those two keep precedence.
                        || (d == '-' && !matches!(bytes.get(i + 1), Some(&'-') | Some(&'>')));
                    if !continues {
                        break;
                    }
                    if i - start >= MAX_IDENTIFIER_CHARS {
                        return Err(LexError {
                            msg: format!("标识符长度超过上限 {MAX_IDENTIFIER_CHARS} 个字符"),
                            line: start_line,
                            col: start_col,
                        });
                    }
                    i += 1;
                    col += 1;
                }
                let s: String = bytes[start..i].iter().collect();
                let tok = match s.as_str() {
                    "_" => Tok::Underscore,
                    "forall" | "Pi" | "pi" => Tok::Forall,
                    "fun" | "lambda" => Tok::Lambda,
                    _ => Tok::Ident(s),
                };
                out.push(Token {
                    tok,
                    line,
                    col: start_col,
                });
            }
            other => {
                return Err(LexError {
                    // A raw character in a diagnostic can forge a line or drive
                    // the terminal. `char`'s Debug escapes it, but as a
                    // lowercase, unpadded code point (`'\u{1b}'`); reuse the
                    // shared escaping so this message spells control and
                    // format characters as `'\u{001B}'`, like the rest of the
                    // tool.
                    msg: format!("无法识别的字符 '{}'", escape_control(&other.to_string())),
                    line,
                    col,
                });
            }
        }
    }
    out.push(Token {
        tok: Tok::Eof,
        line,
        col,
    });
    Ok(out)
}

/// CJK ideographs are identifier characters here. This is the one place the
/// language is deliberately not ASCII: legal and philosophical terms are
/// written in Chinese, and forcing pinyin would be a tax with no benefit.
fn is_cjk(c: char) -> bool {
    matches!(c as u32,
        0x3400..=0x4DBF | 0x4E00..=0x9FFF | 0xF900..=0xFAFF | 0x20000..=0x2FA1F)
}

#[derive(Debug, Clone)]
pub struct LexError {
    pub msg: String,
    pub line: usize,
    pub col: usize,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "第 {} 行第 {} 列：{}", self.line, self.col, self.msg)
    }
}
impl std::error::Error for LexError {}
