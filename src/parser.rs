// chyp-rs: a Rust port of part of Chyp.
//
// Derived from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// file chyp/parser.py, by Aleks Kissinger and the Chyp contributors.
//
// chyp/parser.py carries this notice:
//
//         chyp - An interactive theorem prover for string diagrams
//         Copyright (C) 2022 - Aleks Kissinger
//
//     Licensed under the Apache License, Version 2.0 (the "License");
//     you may not use this file except in compliance with the License.
//     You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//     Unless required by applicable law or agreed to in writing, software
//     distributed under the License is distributed on an "AS IS" BASIS,
//     WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//     See the License for the specific language governing permissions and
//     limitations under the License.
//
// Modified by the chyp-rs contributors, 2026. Changes from the original:
//   - the Lark LALR grammar is replaced by a hand-written lexer and
//     recursive-descent parser for a subset of it, producing an AST
//     (state.rs builds graphs, rules and parts from it, as upstream's
//     Transformer does);
//   - kept as upstream: `*` binds tighter than `;` and both associate to the
//     right (Lark's LALR resolves the grammar's conflicts by shifting);
//     keywords are contextual, as with Lark's contextual lexer (a name may
//     be spelled like a keyword, and where no name may occur a keyword is
//     split off the front of a longer word, so `genf` is `gen f`);
//     `LHS`/`RHS` right after `=` in a rule or theorem are a syntax error;
//     `#` comments; tactic arguments are raw text up to `,`, `(` or `)` with
//     only whitespace skipped before them;
//   - not ported (each is a syntax error here): `import`, generator colours,
//     typed or sized wires (`A`, `u`, `u^2`, `None`, `id[T]`, `sw[T]`),
//     redistributers `rd[...]`, one-way rules (`<=`, `~>`), converse
//     rewrites (`rewrite -name`) and `?` holes; nor are reading and caching
//     files (`parse_cache`) and nested parsing for imports (`parent`,
//     `namespace`, import depth);
//   - `;` and `*` chains are parsed iteratively into flat lists; parentheses
//     may nest at most MAX_NESTING deep and generator arities are at most
//     MAX_WIRES (upstream raises RecursionError from 493 levels and
//     has no arity limit);
//   - parse error messages are chyp-rs's own ("Parse error: unexpected X,
//     expected Y") and report the same line as upstream, which prints Lark's
//     context excerpt.

//! Lexer and parser for the supported subset of Chyp's theory language.

use std::fmt;

/// Where a node starts in the source: 1-based line, and character offsets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Pos {
    pub line: usize,
    pub start: usize,
    pub end: usize,
}

/// A term. `a ; b ; c` is one `Seq` of three operands, meaning
/// `a ; (b ; c)` (upstream's chains associate to the right); likewise `Par`.
/// Chains are flat so that long ones need no recursion.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Seq(Vec<Term>),
    Par(Vec<Term>),
    Nested(Box<Term>, Pos),
    /// `sw` (= `sw[1, 0]`) or `sw[i0, i1, ...]`.
    Perm(Option<Vec<u64>>, Pos),
    Id(Pos),
    Id0(Pos),
    Ref(String, Pos),
}

/// Terms can be nested deeply; drop them without recursion.
impl Drop for Term {
    fn drop(&mut self) {
        let mut stack: Vec<Term> = Vec::new();
        self.take_children(&mut stack);
        while let Some(mut t) = stack.pop() {
            t.take_children(&mut stack);
        }
    }
}

impl Term {
    /// Move this term's sub-terms into `out`, leaving it without any.
    fn take_children(&mut self, out: &mut Vec<Term>) {
        match self {
            Term::Seq(items) | Term::Par(items) => out.append(items),
            Term::Nested(inner, _) => out.push(std::mem::replace(&mut **inner, Term::Id0(Pos::default()))),
            _ => {}
        }
    }

    /// Where the term starts (for a chain: where its first operand starts).
    pub fn pos(&self) -> Pos {
        match self {
            Term::Seq(items) | Term::Par(items) => items[0].pos(),
            Term::Nested(_, p) | Term::Perm(_, p) | Term::Id(p) | Term::Id0(p) | Term::Ref(_, p) => *p,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SideTok {
    Lhs,
    Rhs,
}

/// The right-hand side of a rewrite step.
#[derive(Debug, Clone, PartialEq)]
pub enum Hole {
    Term(Term),
    Side(SideTok),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Tactic {
    pub name: String,
    pub args: Vec<String>,
}

/// `= term [by tactic]`.
#[derive(Debug, Clone, PartialEq)]
pub struct RewriteStep {
    /// From the `=` to the end of the step.
    pub pos: Pos,
    pub hole: Hole,
    pub hole_pos: Pos,
    pub tactic: Option<Tactic>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProofStep {
    Apply {
        tactic: Tactic,
        pos: Pos,
    },
    Rewrite {
        side: SideTok,
        steps: Vec<RewriteStep>,
        pos: Pos,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Proof {
    pub start: Pos,
    pub steps: Vec<ProofStep>,
    pub end: Pos,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Gen {
        name: String,
        n_in: usize,
        n_out: usize,
        pos: Pos,
    },
    Let {
        name: String,
        term: Term,
        pos: Pos,
    },
    Def {
        name: String,
        term: Term,
        pos: Pos,
    },
    Rule {
        name: String,
        lhs: Term,
        rhs: Term,
        pos: Pos,
    },
    Rewrite {
        name: String,
        term: Term,
        steps: Vec<RewriteStep>,
        pos: Pos,
    },
    Show {
        name: String,
        name_pos: Pos,
        pos: Pos,
    },
    Theorem {
        name: String,
        lhs: Term,
        rhs: Term,
        pos: Pos,
        proof: Option<Proof>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

/// Words that are keywords at the start of a term. Lark's contextual lexer
/// treats a word as a keyword only where that keyword may occur, so these are
/// the only identifiers a term cannot refer to (`rd` is upstream's
/// redistributer keyword, which chyp-rs does not support). Statement and
/// proof keywords are recognised where a statement or proof step may start;
/// names (after `gen`, `let`, `show`, ...) and tactics may be any identifier,
/// as upstream (so `apply rule(-gg)` names the `rule` tactic).
const TERM_KEYWORDS: &[&str] = &["sw", "id", "id0", "rd"];

/// Keywords that may start a statement (upstream's, including `import`).
const STATEMENT_KEYWORDS: &[&str] = &[
    "gen",
    "def",
    "let",
    "rule",
    "rewrite",
    "show",
    "theorem",
    "lemma",
    "proposition",
    "import",
];
/// Keywords that may start a proof step.
const PROOF_KEYWORDS: &[&str] = &["apply", "rewrite", "qed"];

/// Deepest parenthesis nesting accepted. Upstream accepts at most 492 levels
/// (deeper, it raises RecursionError); chyp-rs accepts everything upstream
/// does and reports deeper nesting as a syntax error. (Its parser and term
/// evaluation do not recurse, so this is not a stack limit.)
pub const MAX_NESTING: usize = 500;
/// Largest generator arity accepted (upstream has no limit, but builds every
/// wire, so far larger arities exhaust memory there too).
pub const MAX_WIRES: u64 = 65536;

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Ident(String),
    Int(u64),
    Colon,
    Arrow,
    Eq,
    EqEq,
    Semi,
    Star,
    LParen,
    RParen,
    LBrack,
    RBrack,
    Comma,
    Minus,
    Eof,
}

impl Tok {
    fn describe(&self) -> String {
        match self {
            Tok::Ident(s) => format!("'{}'", s),
            Tok::Int(n) => format!("'{}'", n),
            Tok::Colon => "':'".into(),
            Tok::Arrow => "'->'".into(),
            Tok::Eq => "'='".into(),
            Tok::EqEq => "'=='".into(),
            Tok::Semi => "';'".into(),
            Tok::Star => "'*'".into(),
            Tok::LParen => "'('".into(),
            Tok::RParen => "')'".into(),
            Tok::LBrack => "'['".into(),
            Tok::RBrack => "']'".into(),
            Tok::Comma => "','".into(),
            Tok::Minus => "'-'".into(),
            Tok::Eof => "end of input".into(),
        }
    }
}

#[derive(Debug, Clone)]
struct Token {
    tok: Tok,
    line: usize,
    start: usize,
    end: usize,
}

struct Parser {
    src: Vec<char>,
    i: usize,
    line: usize,
    peeked: Option<Token>,
    /// End offset and line of the last consumed token.
    last_end: usize,
    last_line: usize,
}

type PResult<T> = Result<T, ParseError>;

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '.'
}

impl Parser {
    fn new(src: &str) -> Parser {
        Parser {
            src: src.chars().collect(),
            i: 0,
            line: 1,
            peeked: None,
            last_end: 0,
            last_line: 1,
        }
    }

    fn bump(&mut self) -> char {
        let c = self.src[self.i];
        self.i += 1;
        if c == '\n' {
            self.line += 1;
        }
        c
    }

    /// Skip whitespace (Lark's `WS`: space, tab, form feed, CR, LF).
    fn skip_ws(&mut self) {
        while self.i < self.src.len() && matches!(self.src[self.i], ' ' | '\t' | '\n' | '\r' | '\x0c') {
            self.bump();
        }
    }

    /// Skip whitespace and `#` comments.
    fn skip_trivia(&mut self) {
        while self.i < self.src.len() {
            let c = self.src[self.i];
            if matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0c') {
                self.bump();
            } else if c == '#' {
                while self.i < self.src.len() && self.src[self.i] != '\n' {
                    self.bump();
                }
            } else {
                break;
            }
        }
    }

    fn lex(&mut self) -> PResult<Token> {
        self.skip_trivia();
        let line = self.line;
        let start = self.i;
        if self.i >= self.src.len() {
            return Ok(Token {
                tok: Tok::Eof,
                line: self.last_line,
                start,
                end: start,
            });
        }
        let c = self.bump();
        let tok = match c {
            ':' => Tok::Colon,
            ';' => Tok::Semi,
            '*' => Tok::Star,
            '(' => Tok::LParen,
            ')' => Tok::RParen,
            '[' => Tok::LBrack,
            ']' => Tok::RBrack,
            ',' => Tok::Comma,
            '-' => {
                if self.i < self.src.len() && self.src[self.i] == '>' {
                    self.bump();
                    Tok::Arrow
                } else {
                    Tok::Minus
                }
            }
            '=' => {
                if self.i < self.src.len() && self.src[self.i] == '=' {
                    self.bump();
                    Tok::EqEq
                } else {
                    Tok::Eq
                }
            }
            c if c.is_ascii_digit() => {
                let mut s = String::from(c);
                while self.i < self.src.len() && self.src[self.i].is_ascii_digit() {
                    s.push(self.bump());
                }
                match s.parse::<u64>() {
                    Ok(n) => Tok::Int(n),
                    Err(_) => {
                        return Err(ParseError {
                            line,
                            message: format!("Parse error: number too large: {}", s),
                        })
                    }
                }
            }
            c if is_ident_start(c) => {
                let mut s = String::from(c);
                while self.i < self.src.len() && is_ident_char(self.src[self.i]) {
                    s.push(self.bump());
                }
                Tok::Ident(s)
            }
            other => {
                return Err(ParseError {
                    line,
                    message: format!("Parse error: unexpected character {:?}", other),
                });
            }
        };
        Ok(Token {
            tok,
            line,
            start,
            end: self.i,
        })
    }

    fn peek(&mut self) -> PResult<&Token> {
        if self.peeked.is_none() {
            let t = self.lex()?;
            self.peeked = Some(t);
        }
        Ok(self.peeked.as_ref().unwrap())
    }

    fn next(&mut self) -> PResult<Token> {
        let t = match self.peeked.take() {
            Some(t) => t,
            None => self.lex()?,
        };
        if t.tok != Tok::Eof {
            self.last_end = t.end;
            self.last_line = t.line;
        }
        Ok(t)
    }

    fn unexpected<T>(&self, t: &Token, expected: &str) -> PResult<T> {
        Err(ParseError {
            line: t.line,
            message: format!("Parse error: unexpected {}, expected {}", t.tok.describe(), expected),
        })
    }

    fn peek_is_kw(&mut self, kw: &str) -> PResult<bool> {
        Ok(matches!(&self.peek()?.tok, Tok::Ident(s) if s == kw))
    }

    /// At a point where upstream's grammar accepts one of `keywords` but no
    /// identifier, Lark's contextual lexer matches a keyword as a prefix: so
    /// `genf` is `gen f` and `proofqed` is `proof qed`. Split the peeked
    /// identifier the same way (no keyword in these sets is a prefix of
    /// another, so the longest match is the only one).
    fn split_keyword(&mut self, keywords: &[&[&str]]) -> PResult<()> {
        let t = self.peek()?.clone();
        let Tok::Ident(s) = &t.tok else { return Ok(()) };
        let found = keywords
            .iter()
            .flat_map(|set| set.iter())
            .filter(|kw| s.len() > kw.len() && s.starts_with(**kw))
            .max_by_key(|kw| kw.len());
        if let Some(kw) = found {
            let end = t.start + kw.chars().count();
            self.peeked = Some(Token {
                tok: Tok::Ident(kw.to_string()),
                line: t.line,
                start: t.start,
                end,
            });
            // Identifiers hold no newlines, so the line is unchanged.
            self.i = end;
        }
        Ok(())
    }

    fn expect(&mut self, want: Tok, what: &str) -> PResult<Token> {
        let t = self.next()?;
        if t.tok == want {
            Ok(t)
        } else {
            self.unexpected(&t, what)
        }
    }

    fn expect_kw(&mut self, kw: &str) -> PResult<Token> {
        let t = self.next()?;
        match &t.tok {
            Tok::Ident(s) if s == kw => Ok(t),
            _ => self.unexpected(&t, &format!("'{}'", kw)),
        }
    }

    /// Any identifier (a name or tactic position: no keywords apply there).
    fn ident(&mut self, what: &str) -> PResult<(String, Token)> {
        let t = self.next()?;
        match &t.tok {
            Tok::Ident(s) => Ok((s.clone(), t.clone())),
            _ => self.unexpected(&t, what),
        }
    }

    fn int(&mut self) -> PResult<u64> {
        let t = self.next()?;
        match t.tok {
            Tok::Int(n) => Ok(n),
            _ => self.unexpected(&t, "a number"),
        }
    }

    fn pos_from(&self, t: &Token) -> Pos {
        Pos {
            line: t.line,
            start: t.start,
            end: self.last_end,
        }
    }

    /// A generator's input or output count.
    fn arity(&mut self) -> PResult<usize> {
        let t = self.peek()?.clone();
        let n = self.int()?;
        if n > MAX_WIRES {
            return Err(ParseError {
                line: t.line,
                message: format!("Parse error: arity {} is over the limit of {}", n, MAX_WIRES),
            });
        }
        Ok(n as usize)
    }

    /// The right-hand side of a rule or theorem. In upstream's LALR table the
    /// state after `=`/`==` is shared with rewrite steps, whose holes may be
    /// `LHS`/`RHS`, so there those words are keywords and a parse error.
    fn formula_rhs(&mut self) -> PResult<Term> {
        let t = self.peek()?.clone();
        if matches!(&t.tok, Tok::Ident(s) if s == "LHS" || s == "RHS") {
            return self.unexpected(&t, "a term");
        }
        self.term()
    }

    /// `=` or `==`.
    fn eq(&mut self) -> PResult<Token> {
        let t = self.next()?;
        match t.tok {
            Tok::Eq | Tok::EqEq => Ok(t),
            _ => self.unexpected(&t, "'='"),
        }
    }

    fn is_eq(&mut self) -> PResult<bool> {
        Ok(matches!(self.peek()?.tok, Tok::Eq | Tok::EqEq))
    }

    // term     := par_term ( ";" par_term )*
    // par_term := atom ( "*" atom )*
    // atom     := "(" term ")" | sw [ "[" n ("," n)+ "]" ] | id | id0 | NAME
    //
    // Parsed with an explicit stack of open parentheses rather than by
    // recursion, so deep nesting costs heap, not call stack.
    fn term(&mut self) -> PResult<Term> {
        /// A term being built: its finished `;` operands, the `*` operands of
        /// the current one, and the "(" that opened it (none at the bottom).
        struct Frame {
            seq: Vec<Term>,
            par: Vec<Term>,
            open: Option<Token>,
        }
        fn finish(f: &mut Frame) -> Term {
            let mut par = std::mem::take(&mut f.par);
            let p = if par.len() == 1 {
                par.pop().unwrap()
            } else {
                Term::Par(par)
            };
            f.seq.push(p);
            let mut seq = std::mem::take(&mut f.seq);
            if seq.len() == 1 {
                seq.pop().unwrap()
            } else {
                Term::Seq(seq)
            }
        }
        let mut stack = vec![Frame {
            seq: Vec::new(),
            par: Vec::new(),
            open: None,
        }];
        loop {
            // An operand: any number of "(", then a simple atom.
            loop {
                let t = self.peek()?.clone();
                if t.tok != Tok::LParen {
                    let a = self.simple_atom()?;
                    stack.last_mut().unwrap().par.push(a);
                    break;
                }
                if stack.len() > MAX_NESTING {
                    return Err(ParseError {
                        line: t.line,
                        message: format!("Parse error: parentheses nested more than {} deep", MAX_NESTING),
                    });
                }
                self.next()?;
                stack.push(Frame {
                    seq: Vec::new(),
                    par: Vec::new(),
                    open: Some(t),
                });
            }
            // After an operand: "*" or ";" and another operand, ")" closing
            // the innermost "(", or the end of the term.
            loop {
                match self.peek()?.tok {
                    Tok::Star => {
                        self.next()?;
                        break;
                    }
                    Tok::Semi => {
                        self.next()?;
                        let f = stack.last_mut().unwrap();
                        let mut par = std::mem::take(&mut f.par);
                        f.seq.push(if par.len() == 1 {
                            par.pop().unwrap()
                        } else {
                            Term::Par(par)
                        });
                        break;
                    }
                    Tok::RParen if stack.len() > 1 => {
                        self.next()?;
                        let mut f = stack.pop().unwrap();
                        let inner = finish(&mut f);
                        let pos = self.pos_from(f.open.as_ref().unwrap());
                        stack.last_mut().unwrap().par.push(Term::Nested(Box::new(inner), pos));
                    }
                    _ if stack.len() > 1 => {
                        let t = self.peek()?.clone();
                        return self.unexpected(&t, "')'");
                    }
                    _ => return Ok(finish(&mut stack[0])),
                }
            }
        }
    }

    /// An atom other than a parenthesised term.
    fn simple_atom(&mut self) -> PResult<Term> {
        let t = self.next()?;
        match &t.tok {
            Tok::Ident(s) if s == "sw" => {
                if self.peek()?.tok == Tok::LBrack {
                    self.next()?;
                    // perm_indices : num ("," num)+  -- at least two indices
                    let mut idx = vec![self.int()?];
                    loop {
                        let n = self.next()?;
                        match n.tok {
                            Tok::Comma => idx.push(self.int()?),
                            Tok::RBrack if idx.len() >= 2 => break,
                            _ => return self.unexpected(&n, if idx.len() >= 2 { "',' or ']'" } else { "','" }),
                        }
                    }
                    Ok(Term::Perm(Some(idx), self.pos_from(&t)))
                } else {
                    Ok(Term::Perm(None, self.pos_from(&t)))
                }
            }
            Tok::Ident(s) if s == "id" => Ok(Term::Id(self.pos_from(&t))),
            Tok::Ident(s) if s == "id0" => Ok(Term::Id0(self.pos_from(&t))),
            Tok::Ident(s) if !TERM_KEYWORDS.contains(&s.as_str()) => Ok(Term::Ref(s.clone(), self.pos_from(&t))),
            _ => self.unexpected(&t, "a term"),
        }
    }

    /// tactic : ["-"] IDENT | IDENT "(" [ARG ("," ARG)*] ")"
    fn tactic(&mut self) -> PResult<Tactic> {
        if self.peek()?.tok == Tok::Minus {
            self.next()?;
            let (name, _) = self.ident("a rule name")?;
            return Ok(Tactic {
                name: "rule".into(),
                args: vec![format!("-{}", name)],
            });
        }
        let (name, _) = self.ident("a rule or tactic name")?;
        if self.peek()?.tok == Tok::LParen {
            self.next()?;
            let args = self.tactic_args()?;
            Ok(Tactic { name, args })
        } else {
            Ok(Tactic {
                name: "rule".into(),
                args: vec![name],
            })
        }
    }

    /// Raw tactic arguments (`/[^(),]+/`), after the "(" has been consumed.
    /// As in upstream's lexer, only whitespace is skipped before an argument;
    /// anything else up to `,`, `(` or `)` is the argument, including inner
    /// and trailing whitespace and a leading `#` (upstream's lexer tries the
    /// argument pattern before the comment pattern). Errors are reported on
    /// the line Lark reports: at end of input, where the last token (the
    /// argument, or the `(` / `,` before it) starts; otherwise at the
    /// unexpected character.
    fn tactic_args(&mut self) -> PResult<Vec<String>> {
        debug_assert!(self.peeked.is_none());
        let mut args = Vec::new();
        loop {
            self.skip_ws();
            let line = self.line;
            let start = self.i;
            while self.i < self.src.len() && !matches!(self.src[self.i], '(' | ')' | ',') {
                self.bump();
            }
            let arg: String = self.src[start..self.i].iter().collect();
            if self.i >= self.src.len() {
                let line = if arg.is_empty() { self.last_line } else { line };
                return Err(ParseError {
                    line,
                    message: "Parse error: unclosed tactic arguments".into(),
                });
            }
            let c = self.src[self.i];
            if arg.is_empty() {
                // Only `f()` (no arguments at all) may have an empty argument.
                if c == ')' && args.is_empty() {
                    self.bump();
                    self.last_end = self.i;
                    self.last_line = self.line;
                    return Ok(args);
                }
                return Err(ParseError {
                    line: self.line,
                    message: format!("Parse error: unexpected {:?} in tactic arguments", c),
                });
            }
            args.push(arg);
            if c == '(' {
                return Err(ParseError {
                    line: self.line,
                    message: "Parse error: unexpected '(' in tactic arguments".into(),
                });
            }
            self.bump();
            self.last_end = self.i;
            self.last_line = self.line;
            if c == ')' {
                return Ok(args);
            }
        }
    }

    /// rewrite_part : ("=" | "==") term_hole ["by" tactic]
    fn rewrite_step(&mut self) -> PResult<RewriteStep> {
        let eq = self.eq()?;
        let hole_tok = self.peek()?.clone();
        let hole = match &hole_tok.tok {
            Tok::Ident(s) if s == "LHS" => {
                self.next()?;
                Hole::Side(SideTok::Lhs)
            }
            Tok::Ident(s) if s == "RHS" => {
                self.next()?;
                Hole::Side(SideTok::Rhs)
            }
            _ => Hole::Term(self.term()?),
        };
        let hole_pos = self.pos_from(&hole_tok);
        self.split_keyword(&[&["by"], STATEMENT_KEYWORDS, PROOF_KEYWORDS])?;
        let tactic = if self.peek_is_kw("by")? {
            self.next()?;
            Some(self.tactic()?)
        } else {
            None
        };
        Ok(RewriteStep {
            pos: self.pos_from(&eq),
            hole,
            hole_pos,
            tactic,
        })
    }

    fn rewrite_steps(&mut self) -> PResult<Vec<RewriteStep>> {
        let mut steps = Vec::new();
        while self.is_eq()? {
            steps.push(self.rewrite_step()?);
        }
        Ok(steps)
    }

    fn statement(&mut self) -> PResult<Stmt> {
        self.split_keyword(&[STATEMENT_KEYWORDS])?;
        let t = self.next()?;
        let kw = match &t.tok {
            Tok::Ident(s) => s.clone(),
            _ => return self.unexpected(&t, "a statement"),
        };
        match kw.as_str() {
            "gen" => {
                let (name, _) = self.ident("a generator name")?;
                self.expect(Tok::Colon, "':'")?;
                let n_in = self.arity()?;
                self.expect(Tok::Arrow, "'->'")?;
                let n_out = self.arity()?;
                Ok(Stmt::Gen {
                    name,
                    n_in,
                    n_out,
                    pos: self.pos_from(&t),
                })
            }
            "let" | "def" => {
                let (name, _) = self.ident("a name")?;
                self.expect(Tok::Eq, "'='")?;
                let term = self.term()?;
                let pos = self.pos_from(&t);
                Ok(if kw == "let" {
                    Stmt::Let { name, term, pos }
                } else {
                    Stmt::Def { name, term, pos }
                })
            }
            "rule" => {
                let (name, _) = self.ident("a rule name")?;
                self.expect(Tok::Colon, "':'")?;
                let lhs = self.term()?;
                self.eq()?;
                let rhs = self.formula_rhs()?;
                Ok(Stmt::Rule {
                    name,
                    lhs,
                    rhs,
                    pos: self.pos_from(&t),
                })
            }
            "rewrite" => {
                let (name, _) = self.ident("a rewrite name")?;
                self.expect(Tok::Colon, "':'")?;
                let term = self.term()?;
                // LHS/RHS parse here too; state.rs reports them as errors.
                let steps = self.rewrite_steps()?;
                Ok(Stmt::Rewrite {
                    name,
                    term,
                    steps,
                    pos: self.pos_from(&t),
                })
            }
            "show" => {
                let (name, nt) = self.ident("a rule name")?;
                let name_pos = Pos {
                    line: nt.line,
                    start: nt.start,
                    end: nt.end,
                };
                Ok(Stmt::Show {
                    name,
                    name_pos,
                    pos: self.pos_from(&t),
                })
            }
            "theorem" | "lemma" | "proposition" => {
                let (name, _) = self.ident("a theorem name")?;
                self.expect(Tok::Colon, "':'")?;
                let lhs = self.term()?;
                self.eq()?;
                let rhs = self.formula_rhs()?;
                let pos = self.pos_from(&t);
                self.split_keyword(&[&["proof"], STATEMENT_KEYWORDS])?;
                let proof = if self.peek_is_kw("proof")? {
                    Some(self.proof()?)
                } else {
                    None
                };
                Ok(Stmt::Theorem {
                    name,
                    lhs,
                    rhs,
                    pos,
                    proof,
                })
            }
            _ => self.unexpected(&t, "a statement"),
        }
    }

    fn proof(&mut self) -> PResult<Proof> {
        let pt = self.expect_kw("proof")?;
        let start = self.pos_from(&pt);
        let mut steps = Vec::new();
        loop {
            self.split_keyword(&[PROOF_KEYWORDS])?;
            let t = self.peek()?.clone();
            match &t.tok {
                Tok::Ident(s) if s == "qed" => {
                    self.next()?;
                    let end = self.pos_from(&t);
                    return Ok(Proof { start, steps, end });
                }
                Tok::Ident(s) if s == "apply" => {
                    self.next()?;
                    let tactic = self.tactic()?;
                    steps.push(ProofStep::Apply {
                        tactic,
                        pos: self.pos_from(&t),
                    });
                }
                Tok::Ident(s) if s == "rewrite" => {
                    self.next()?;
                    self.split_keyword(&[&["LHS", "RHS"]])?;
                    let st = self.next()?;
                    let side = match &st.tok {
                        Tok::Ident(s) if s == "LHS" => SideTok::Lhs,
                        Tok::Ident(s) if s == "RHS" => SideTok::Rhs,
                        _ => return self.unexpected(&st, "LHS or RHS"),
                    };
                    let rsteps = self.rewrite_steps()?;
                    steps.push(ProofStep::Rewrite {
                        side,
                        steps: rsteps,
                        pos: self.pos_from(&t),
                    });
                }
                _ => return self.unexpected(&t, "'apply', 'rewrite' or 'qed'"),
            }
        }
    }

    fn file(&mut self) -> PResult<Vec<Stmt>> {
        let mut stmts = Vec::new();
        while self.peek()?.tok != Tok::Eof {
            stmts.push(self.statement()?);
        }
        Ok(stmts)
    }
}

/// Parse a whole theory file. As upstream, a syntax error anywhere means no
/// statements at all.
pub fn parse(src: &str) -> Result<Vec<Stmt>, ParseError> {
    Parser::new(src).file()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Print a term fully bracketed, chains associating to the right.
    fn shape(t: &Term) -> String {
        fn chain(items: &[Term], op: &str) -> String {
            match items {
                [a] => shape(a),
                [a, rest @ ..] => format!("({} {} {})", shape(a), op, chain(rest, op)),
                [] => unreachable!(),
            }
        }
        match t {
            Term::Seq(items) => chain(items, ";"),
            Term::Par(items) => chain(items, "*"),
            Term::Nested(a, _) => shape(a),
            Term::Perm(None, _) => "sw".into(),
            Term::Perm(Some(p), _) => format!("sw{:?}", p),
            Term::Id(_) => "id".into(),
            Term::Id0(_) => "id0".into(),
            Term::Ref(s, _) => s.clone(),
        }
    }

    #[test]
    fn associativity_matches_lark() {
        let stmts = parse("let x = a * a * a ; a ; a * (a ; a)").unwrap();
        let Stmt::Let { term, .. } = &stmts[0] else { panic!() };
        assert_eq!(shape(term), "((a * (a * a)) ; (a ; (a * (a ; a))))");
    }

    /// Accept/reject agreement with upstream's Lark parser, checked by hand
    /// with `chyp.parser.GRAMMAR.parse` at commit 3d28483.
    #[test]
    fn acceptance_matches_lark() {
        let accepted = [
            "gen by : 1 -> 1",
            "let x = rule ; proof",
            "rewrite r : x = x by rule(LHS)",
            "gen id : 1 -> 1",
            "let x = LHS",
            "rewrite r : f = LHS",
            "show gen",
            "let gen = f",
            "rewrite r : f = f by -rule",
            "theorem t : f = f proof apply rule(x) qed",
            "theorem t : f = f proof rewrite LHS = proof qed",
            "let x = to",
            "let x = import",
            "gen f : 1 -> 1 rule r : f = f lemma l : f = f",
            "rewrite r : f\n = f by ff\n gen g : 1 -> 1",
            "let x = f ; (g * h) ; sw[2,0,1]",
            "rewrite r : f == g by x()",
            "rewrite r : f = g by x( )",
            "rewrite r: f = g by x(a b, c)",
        ];
        for src in accepted {
            assert!(parse(src).is_ok(), "should parse: {:?}: {:?}", src, parse(src));
        }
        // `sw[1]` parses upstream as a typed swap `sw[T]` (not supported here).
        let rejected = [
            "let x = id ; rd",
            "foo",
            "apply ff",
            "rewrite r : f = g by x(a,)",
            "rewrite r : f = g by x(,a)",
        ];
        for src in rejected {
            assert!(parse(src).is_err(), "should not parse: {:?}", src);
        }
    }

    #[test]
    fn tactics_and_keywords() {
        let src = "rewrite r : f\n  = g by simp( A.x , B )\n  = h by -ff\n  = k\n  = idx by foo()";
        let stmts = parse(src).unwrap();
        let Stmt::Rewrite { steps, .. } = &stmts[0] else {
            panic!()
        };
        assert_eq!(
            steps[0].tactic,
            Some(Tactic {
                name: "simp".into(),
                args: vec!["A.x ".into(), "B ".into()]
            })
        );
        assert_eq!(
            steps[1].tactic,
            Some(Tactic {
                name: "rule".into(),
                args: vec!["-ff".into()]
            })
        );
        assert_eq!(steps[2].tactic, None);
        assert_eq!(
            steps[3].tactic,
            Some(Tactic {
                name: "foo".into(),
                args: vec![]
            })
        );
        assert_eq!(steps[3].pos.line, 5);
        // Keywords are contextual, as with Lark's contextual lexer.
        assert!(parse("gen by : 1 -> 1\nlet x = rule ; proof\nrewrite r : x = x by rule(LHS)").is_ok());
        assert!(parse("let x = id ; rd").is_err());
        assert!(parse("foo").is_err());
        assert_eq!(
            parse("gen f : 1 -> 1\nrule r : f = f\ngen g : 1 ->\nrule s : g = g")
                .unwrap_err()
                .line,
            4
        );
    }
}
