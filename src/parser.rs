// Ported from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// file chyp/parser.py. Copyright (C) 2022 Aleks Kissinger.
// Licensed under the Apache License, Version 2.0.
//
// Changes from the original (chyp-rs contributors, 2026): the Lark LALR
// grammar is replaced by a hand-written lexer and recursive-descent parser
// for a subset of it, producing an AST (state.rs then builds graphs, rules
// and parts from it, as upstream's Transformer does). Kept as upstream:
// `*` binds tighter than `;`, both associate to the right (Lark's LALR
// resolves the grammar's conflicts by shifting), keywords are contextual
// (as with Lark's contextual lexer), `#` comments, and tactic arguments are
// raw text up to `,` or `)`. Not ported (each is a parse error here):
// `import`, generator colours, typed or sized wires (`A`, `u^2`, `None`,
// `id[T]`, `sw[T]`), redistributers `rd[...]`, one-way rules (`<=`, `~>`),
// converse rewrites (`rewrite -name`), and `?` holes.

//! Lexer and parser for the supported subset of Chyp's theory language.

use std::fmt;

/// Where a node starts in the source: 1-based line, and character offsets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Pos {
    pub line: usize,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Seq(Box<Term>, Box<Term>, Pos),
    Par(Box<Term>, Box<Term>, Pos),
    Nested(Box<Term>, Pos),
    /// `sw` (= `sw[1, 0]`) or `sw[i0, i1, ...]`.
    Perm(Option<Vec<usize>>, Pos),
    Id(Pos),
    Id0(Pos),
    Ref(String, Pos),
}

impl Term {
    pub fn pos(&self) -> Pos {
        match self {
            Term::Seq(_, _, p)
            | Term::Par(_, _, p)
            | Term::Nested(_, p)
            | Term::Perm(_, p)
            | Term::Id(p)
            | Term::Id0(p)
            | Term::Ref(_, p) => *p,
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
    Apply { tactic: Tactic, pos: Pos },
    Rewrite { side: SideTok, steps: Vec<RewriteStep>, pos: Pos },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Proof {
    pub start: Pos,
    pub steps: Vec<ProofStep>,
    pub end: Pos,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Gen { name: String, n_in: usize, n_out: usize, pos: Pos },
    Let { name: String, term: Term, pos: Pos },
    Def { name: String, term: Term, pos: Pos },
    Rule { name: String, lhs: Term, rhs: Term, pos: Pos },
    Rewrite { name: String, term: Term, steps: Vec<RewriteStep>, pos: Pos },
    Show { name: String, name_pos: Pos, pos: Pos },
    Theorem { name: String, lhs: Term, rhs: Term, pos: Pos, proof: Option<Proof> },
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

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Ident(String),
    Int(usize),
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
        Parser { src: src.chars().collect(), i: 0, line: 1, peeked: None, last_end: 0, last_line: 1 }
    }

    fn bump(&mut self) -> char {
        let c = self.src[self.i];
        self.i += 1;
        if c == '\n' {
            self.line += 1;
        }
        c
    }

    /// Skip whitespace and `#` comments.
    fn skip_trivia(&mut self) {
        while self.i < self.src.len() {
            let c = self.src[self.i];
            if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' {
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
            return Ok(Token { tok: Tok::Eof, line: self.last_line, start, end: start });
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
                match s.parse::<usize>() {
                    Ok(n) => Tok::Int(n),
                    Err(_) => return Err(ParseError { line, message: format!("Parse error: number too large: {}", s) }),
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
                return Err(ParseError { line, message: format!("Parse error: unexpected character {:?}", other) });
            }
        };
        Ok(Token { tok, line, start, end: self.i })
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

    fn int(&mut self) -> PResult<usize> {
        let t = self.next()?;
        match t.tok {
            Tok::Int(n) => Ok(n),
            _ => self.unexpected(&t, "a number"),
        }
    }

    fn pos_from(&self, t: &Token) -> Pos {
        Pos { line: t.line, start: t.start, end: self.last_end }
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

    // term     := par_term [ ";" term ]
    // par_term := atom [ "*" par_term ]
    fn term(&mut self) -> PResult<Term> {
        let first = self.peek()?.clone();
        let left = self.par_term()?;
        if self.peek()?.tok == Tok::Semi {
            self.next()?;
            let right = self.term()?;
            let pos = self.pos_from(&first);
            Ok(Term::Seq(Box::new(left), Box::new(right), pos))
        } else {
            Ok(left)
        }
    }

    fn par_term(&mut self) -> PResult<Term> {
        let first = self.peek()?.clone();
        let left = self.atom()?;
        if self.peek()?.tok == Tok::Star {
            self.next()?;
            let right = self.par_term()?;
            let pos = self.pos_from(&first);
            Ok(Term::Par(Box::new(left), Box::new(right), pos))
        } else {
            Ok(left)
        }
    }

    fn atom(&mut self) -> PResult<Term> {
        let t = self.next()?;
        match &t.tok {
            Tok::LParen => {
                let inner = self.term()?;
                self.expect(Tok::RParen, "')'")?;
                Ok(Term::Nested(Box::new(inner), self.pos_from(&t)))
            }
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
            return Ok(Tactic { name: "rule".into(), args: vec![format!("-{}", name)] });
        }
        let (name, _) = self.ident("a rule or tactic name")?;
        if self.peek()?.tok == Tok::LParen {
            self.next()?;
            let args = self.tactic_args()?;
            Ok(Tactic { name, args })
        } else {
            Ok(Tactic { name: "rule".into(), args: vec![name] })
        }
    }

    /// Raw tactic arguments (`/[^(),]+/`), after the "(" has been consumed.
    /// As in upstream's lexer, leading whitespace and comments are skipped but
    /// anything else up to `,` or `)` (including inner and trailing spaces) is
    /// part of the argument.
    fn tactic_args(&mut self) -> PResult<Vec<String>> {
        debug_assert!(self.peeked.is_none());
        let mut args = Vec::new();
        loop {
            self.skip_trivia();
            let line = self.line;
            let start = self.i;
            while self.i < self.src.len() && !matches!(self.src[self.i], '(' | ')' | ',') {
                self.bump();
            }
            let arg: String = self.src[start..self.i].iter().collect();
            if self.i >= self.src.len() {
                return Err(ParseError { line: self.line, message: "Parse error: unclosed tactic arguments".into() });
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
                return Err(ParseError { line, message: format!("Parse error: unexpected {:?} in tactic arguments", c) });
            }
            args.push(arg);
            self.bump();
            self.last_end = self.i;
            self.last_line = self.line;
            match c {
                ',' => continue,
                ')' => return Ok(args),
                _ => return Err(ParseError { line, message: "Parse error: unexpected '(' in tactic arguments".into() }),
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
        let tactic = if self.peek_is_kw("by")? {
            self.next()?;
            Some(self.tactic()?)
        } else {
            None
        };
        Ok(RewriteStep { pos: self.pos_from(&eq), hole, hole_pos, tactic })
    }

    fn rewrite_steps(&mut self) -> PResult<Vec<RewriteStep>> {
        let mut steps = Vec::new();
        while self.is_eq()? {
            steps.push(self.rewrite_step()?);
        }
        Ok(steps)
    }

    fn statement(&mut self) -> PResult<Stmt> {
        let t = self.next()?;
        let kw = match &t.tok {
            Tok::Ident(s) => s.clone(),
            _ => return self.unexpected(&t, "a statement"),
        };
        match kw.as_str() {
            "gen" => {
                let (name, _) = self.ident("a generator name")?;
                self.expect(Tok::Colon, "':'")?;
                let n_in = self.int()?;
                self.expect(Tok::Arrow, "'->'")?;
                let n_out = self.int()?;
                Ok(Stmt::Gen { name, n_in, n_out, pos: self.pos_from(&t) })
            }
            "let" | "def" => {
                let (name, _) = self.ident("a name")?;
                self.expect(Tok::Eq, "'='")?;
                let term = self.term()?;
                let pos = self.pos_from(&t);
                Ok(if kw == "let" { Stmt::Let { name, term, pos } } else { Stmt::Def { name, term, pos } })
            }
            "rule" => {
                let (name, _) = self.ident("a rule name")?;
                self.expect(Tok::Colon, "':'")?;
                let lhs = self.term()?;
                self.eq()?;
                let rhs = self.term()?;
                Ok(Stmt::Rule { name, lhs, rhs, pos: self.pos_from(&t) })
            }
            "rewrite" => {
                let (name, _) = self.ident("a rewrite name")?;
                self.expect(Tok::Colon, "':'")?;
                let term = self.term()?;
                // LHS/RHS parse here too; state.rs reports them as errors.
                let steps = self.rewrite_steps()?;
                Ok(Stmt::Rewrite { name, term, steps, pos: self.pos_from(&t) })
            }
            "show" => {
                let (name, nt) = self.ident("a rule name")?;
                let name_pos = Pos { line: nt.line, start: nt.start, end: nt.end };
                Ok(Stmt::Show { name, name_pos, pos: self.pos_from(&t) })
            }
            "theorem" | "lemma" | "proposition" => {
                let (name, _) = self.ident("a theorem name")?;
                self.expect(Tok::Colon, "':'")?;
                let lhs = self.term()?;
                self.eq()?;
                let rhs = self.term()?;
                let pos = self.pos_from(&t);
                let proof = if self.peek_is_kw("proof")? { Some(self.proof()?) } else { None };
                Ok(Stmt::Theorem { name, lhs, rhs, pos, proof })
            }
            _ => self.unexpected(&t, "a statement"),
        }
    }

    fn proof(&mut self) -> PResult<Proof> {
        let pt = self.expect_kw("proof")?;
        let start = self.pos_from(&pt);
        let mut steps = Vec::new();
        loop {
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
                    steps.push(ProofStep::Apply { tactic, pos: self.pos_from(&t) });
                }
                Tok::Ident(s) if s == "rewrite" => {
                    self.next()?;
                    let st = self.next()?;
                    let side = match &st.tok {
                        Tok::Ident(s) if s == "LHS" => SideTok::Lhs,
                        Tok::Ident(s) if s == "RHS" => SideTok::Rhs,
                        _ => return self.unexpected(&st, "LHS or RHS"),
                    };
                    let rsteps = self.rewrite_steps()?;
                    steps.push(ProofStep::Rewrite { side, steps: rsteps, pos: self.pos_from(&t) });
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

    fn shape(t: &Term) -> String {
        match t {
            Term::Seq(a, b, _) => format!("({} ; {})", shape(a), shape(b)),
            Term::Par(a, b, _) => format!("({} * {})", shape(a), shape(b)),
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
        let rejected = ["let x = id ; rd", "foo", "apply ff", "rewrite r : f = g by x(a,)", "rewrite r : f = g by x(,a)"];
        for src in rejected {
            assert!(parse(src).is_err(), "should not parse: {:?}", src);
        }
    }

    #[test]
    fn tactics_and_keywords() {
        let src = "rewrite r : f\n  = g by simp( A.x , B )\n  = h by -ff\n  = k\n  = idx by foo()";
        let stmts = parse(src).unwrap();
        let Stmt::Rewrite { steps, .. } = &stmts[0] else { panic!() };
        assert_eq!(steps[0].tactic, Some(Tactic { name: "simp".into(), args: vec!["A.x ".into(), "B ".into()] }));
        assert_eq!(steps[1].tactic, Some(Tactic { name: "rule".into(), args: vec!["-ff".into()] }));
        assert_eq!(steps[2].tactic, None);
        assert_eq!(steps[3].tactic, Some(Tactic { name: "foo".into(), args: vec![] }));
        assert_eq!(steps[3].pos.line, 5);
        // Keywords are contextual, as with Lark's contextual lexer.
        assert!(parse("gen by : 1 -> 1\nlet x = rule ; proof\nrewrite r : x = x by rule(LHS)").is_ok());
        assert!(parse("let x = id ; rd").is_err());
        assert!(parse("foo").is_err());
        assert_eq!(parse("gen f : 1 -> 1\nrule r : f = f\ngen g : 1 ->\nrule s : g = g").unwrap_err().line, 4);
    }
}
