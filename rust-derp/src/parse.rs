use crate::sym::Interner;
use crate::types::*;
use crate::core::{atom};

// -- Tokenizer ----------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Ident(String),  // predicate or variable name (may contain - / _ ' internally)
    Blank,          // standalone _
    Nat(i32),
    Str(String),
    // punctuation
    LParen,
    RParen,
    Comma,
    Dot,
    Eq,
    Bang,
    Question,
    // operators (only when appearing at token-start position, not mid-ident)
    Plus,
    Minus,
    Star,
    Slash,
    // two or more consecutive hyphens at token-start position
    RuleSep,
    Arrow,     // ->  (body on left, head on right)
    ArrowRev,  // <-  (head on left, body on right)
}

fn is_id_char(c: char) -> bool {
    c.is_alphanumeric() || c == '-' || c == '/' || c == '_' || c == '\''
}

fn lex(input: &str) -> Result<Vec<Token>, String> {
    let chars: Vec<char> = input.chars().collect();
    let mut pos = 0;
    let mut tokens = Vec::new();

    while pos < chars.len() {
        let c = chars[pos];

        // Skip whitespace
        if c == ' ' || c == '\n' || c == '\t' || c == '\r' {
            pos += 1;
            continue;
        }

        // Hyphens: two or more → RuleSep; -> → Arrow; single → Minus
        if c == '-' {
            if pos + 1 < chars.len() && chars[pos + 1] == '-' {
                while pos < chars.len() && chars[pos] == '-' {
                    pos += 1;
                }
                tokens.push(Token::RuleSep);
            } else if pos + 1 < chars.len() && chars[pos + 1] == '>' {
                pos += 2;
                tokens.push(Token::Arrow);
            } else {
                pos += 1;
                tokens.push(Token::Minus);
            }
            continue;
        }

        // <- → ArrowRev
        if c == '<' {
            if pos + 1 < chars.len() && chars[pos + 1] == '-' {
                pos += 2;
                tokens.push(Token::ArrowRev);
                continue;
            }
            return Err(format!("unexpected character '<' at byte pos {}", pos));
        }

        // Identifiers: start with letter or #, consume id chars greedily
        if c.is_alphabetic() || c == '#' {
            let start = pos;
            pos += 1;
            while pos < chars.len() && is_id_char(chars[pos]) {
                pos += 1;
            }
            let s: String = chars[start..pos].iter().collect();
            tokens.push(Token::Ident(s));
            continue;
        }

        // _ alone becomes Blank; _var becomes Ident("_var")
        if c == '_' {
            pos += 1;
            if pos < chars.len() && is_id_char(chars[pos]) {
                let start = pos - 1;
                while pos < chars.len() && is_id_char(chars[pos]) {
                    pos += 1;
                }
                let s: String = chars[start..pos].iter().collect();
                tokens.push(Token::Ident(s));
            } else {
                tokens.push(Token::Blank);
            }
            continue;
        }

        // Digits
        if c.is_ascii_digit() {
            let start = pos;
            while pos < chars.len() && chars[pos].is_ascii_digit() {
                pos += 1;
            }
            let s: String = chars[start..pos].iter().collect();
            let n = s.parse::<i32>().map_err(|e| e.to_string())?;
            tokens.push(Token::Nat(n));
            continue;
        }

        // String literal
        if c == '"' {
            pos += 1;
            let mut s = String::new();
            loop {
                if pos >= chars.len() {
                    return Err("unterminated string literal".to_string());
                }
                if chars[pos] == '"' {
                    pos += 1;
                    break;
                }
                s.push(chars[pos]);
                pos += 1;
            }
            tokens.push(Token::Str(s));
            continue;
        }

        // Single-character tokens
        let tok = match c {
            '(' => Token::LParen,
            ')' => Token::RParen,
            ',' => Token::Comma,
            '.' => Token::Dot,
            '=' => Token::Eq,
            '!' => Token::Bang,
            '?' => Token::Question,
            '+' => Token::Plus,
            '*' => Token::Star,
            '/' => Token::Slash,
            other => return Err(format!("unexpected character '{}' at byte pos {}", other, pos)),
        };
        pos += 1;
        tokens.push(tok);
    }

    Ok(tokens)
}

// -- Parser state -------------------------------------------------------------

struct Parser<'a> {
    tokens: Vec<Token>,
    pos: usize,
    intern: &'a mut Interner,
}

type PResult<T> = Result<T, String>;

impl<'a> Parser<'a> {
    fn new(tokens: Vec<Token>, intern: &'a mut Interner) -> Self {
        Parser { tokens, pos: 0, intern }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn expect(&mut self, tok: &Token) -> PResult<()> {
        match self.peek() {
            Some(t) if t == tok => {
                self.advance();
                Ok(())
            }
            other => Err(format!("expected {:?}, got {:?} at token pos {}", tok, other, self.pos)),
        }
    }

    fn predicate(&mut self) -> PResult<String> {
        match self.peek() {
            Some(Token::Ident(s)) if s.starts_with(|c: char| c.is_lowercase() || c == '#') => {
                let s = s.clone();
                self.advance();
                Ok(s)
            }
            other => Err(format!("expected predicate, got {:?} at token pos {}", other, self.pos)),
        }
    }

    fn variable(&mut self) -> PResult<String> {
        match self.peek() {
            Some(Token::Ident(s))
                if s.starts_with(|c: char| c.is_uppercase())
                    || (s.starts_with('_') && s.len() > 1) =>
            {
                let s = s.clone();
                self.advance();
                Ok(s)
            }
            other => Err(format!("expected variable, got {:?} at token pos {}", other, self.pos)),
        }
    }

    fn nat(&mut self) -> PResult<i32> {
        match self.peek() {
            Some(Token::Nat(n)) => {
                let n = *n;
                self.advance();
                Ok(n)
            }
            other => Err(format!("expected number, got {:?} at token pos {}", other, self.pos)),
        }
    }

    fn string_lit(&mut self) -> PResult<String> {
        match self.peek() {
            Some(Token::Str(s)) => {
                let s = s.clone();
                self.advance();
                Ok(s)
            }
            other => Err(format!("expected string, got {:?} at token pos {}", other, self.pos)),
        }
    }

    fn comma_sep<T>(&mut self, f: impl Fn(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        let mut results = Vec::new();
        match f(self) {
            Ok(v) => results.push(v),
            Err(_) => return Ok(results),
        }
        loop {
            let saved = self.pos;
            if self.expect(&Token::Comma).is_err() {
                break;
            }
            match f(self) {
                Ok(v) => results.push(v),
                Err(_) => {
                    self.pos = saved;
                    break;
                }
            }
        }
        Ok(results)
    }

    /// Parse zero or more occurrences of f, stopping on the first failure.
    /// Replaces ws_sep: whitespace separation is handled by the tokenizer.
    fn many<T>(&mut self, f: impl Fn(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        let mut results = Vec::new();
        loop {
            let saved = self.pos;
            match f(self) {
                Ok(v) => results.push(v),
                Err(_) => {
                    self.pos = saved;
                    break;
                }
            }
        }
        Ok(results)
    }

    // -- Term parser ----------------------------------------------------------

    fn term(&mut self) -> PResult<ATerm> {
        let lhs = self.term_primary()?;
        let saved = self.pos;
        let op = match self.peek() {
            Some(Token::Plus)  => BinOp::Plus,
            Some(Token::Minus) => BinOp::Minus,
            Some(Token::Star)  => BinOp::Times,
            Some(Token::Slash) => BinOp::Div,
            _ => {
                self.pos = saved;
                return Ok(lhs);
            }
        };
        self.advance();
        let rhs = self.term_primary()?;
        Ok(abinop(op, lhs, rhs))
    }

    fn term_primary(&mut self) -> PResult<ATerm> {
        // Try choice: ?t
        let saved = self.pos;
        if self.expect(&Token::Question).is_ok() {
            if let Ok(inner) = self.term() {
                return Ok(achoice(inner));
            }
            self.pos = saved;
        }

        // Try plain predicate
        let saved = self.pos;
        if let Ok(name) = self.predicate() {
            if name.starts_with('#') {
                return Ok(apred(Name::Special(name[1..].to_string())));
            } else {
                let sym = self.intern.intern(&name);
                return Ok(apred(Name::Sym(sym)));
            }
        }
        self.pos = saved;

        // Try variable
        let saved = self.pos;
        if let Ok(v) = self.variable() {
            let sym = self.intern.intern(&v);
            return Ok(avar(Name::Sym(sym)));
        }
        self.pos = saved;

        // Try blank
        if matches!(self.peek(), Some(Token::Blank)) {
            self.advance();
            return Ok(ablank());
        }

        // Try number
        let saved = self.pos;
        if let Ok(n) = self.nat() {
            return Ok(anum(n));
        }
        self.pos = saved;

        // Try string
        let saved = self.pos;
        if let Ok(s) = self.string_lit() {
            let sym = self.intern.intern(&s);
            return Ok(astr(Name::Sym(sym)));
        }
        self.pos = saved;

        // Try parenthesized: (pred args...) = application, or (term) = grouping
        let saved = self.pos;
        if self.expect(&Token::LParen).is_ok() {
            let saved2 = self.pos;
            if let Ok(name) = self.predicate() {
                let args = self.many(|p| p.term())?;
                if self.expect(&Token::RParen).is_ok() {
                    let sym = self.intern.intern(&name);
                    return Ok(aapp(Name::Sym(sym), args));
                }
            }
            self.pos = saved2;
            if let Ok(inner) = self.term() {
                if self.expect(&Token::RParen).is_ok() {
                    return Ok(inner);
                }
            }
            self.pos = saved;
        }

        Err(format!("expected term at token pos {}", self.pos))
    }

    // -- Tuple parser ---------------------------------------------------------

    fn tuple(&mut self) -> PResult<Tuple> {
        let terms = self.many(|p| p.term())?;
        Ok(terms.into_iter().collect())
    }

    // -- Expr parser ----------------------------------------------------------

    fn expr(&mut self) -> PResult<Expr> {
        let leaves = self.comma_sep(|p| p.expr_leaf())?;
        let e = leaves.into_iter().fold(Expr::Unit, |acc, leaf| join(acc, leaf));
        Ok(e)
    }

    fn expr_leaf(&mut self) -> PResult<Expr> {
        let saved = self.pos;

        // Try neg: '!' followed by terms
        if self.expect(&Token::Bang).is_ok() {
            let terms = self.many(|p| p.term())?;
            let tuple: Tuple = terms.into_iter().collect();
            return Ok(Expr::NegAtom(tuple));
        }
        self.pos = saved;

        // Try bind: term '=' term
        let saved = self.pos;
        if let Ok(lhs) = self.term() {
            let saved2 = self.pos;
            if self.expect(&Token::Eq).is_ok() {
                let rhs = self.term()?;
                return Ok(Expr::Bind(lhs, rhs));
            }
            self.pos = saved2;
            self.pos = saved;
        } else {
            self.pos = saved;
        }

        // Try tup: many terms → atom
        let terms = self.many(|p| p.term())?;
        let tuple: Tuple = terms.into_iter().collect();
        Ok(atom(tuple))
    }

    // -- Rule parser ----------------------------------------------------------

    fn expr_to_tuples(e: Expr) -> PResult<Vec<Tuple>> {
        match e {
            Expr::Unit => Ok(vec![]),
            Expr::Atom(t) => Ok(vec![t]),
            Expr::Join(a, b) => {
                let mut ts = Self::expr_to_tuples(*a)?;
                ts.extend(Self::expr_to_tuples(*b)?);
                Ok(ts)
            }
            other => Err(format!("expected tuple in head position, got {:?}", other)),
        }
    }

    fn rule(&mut self) -> PResult<Rule> {
        let lhs = self.expr()?;
        match self.peek() {
            Some(Token::RuleSep) | Some(Token::Arrow) => {
                self.advance();
                let heads = self.comma_sep(|p| p.tuple())?;
                Ok(Rule {
                    body: Closure { ctx: Binding::new(), val: lhs },
                    head: heads,
                })
            }
            Some(Token::ArrowRev) => {
                self.advance();
                let body = self.expr()?;
                let heads = Self::expr_to_tuples(lhs)?;
                Ok(Rule {
                    body: Closure { ctx: Binding::new(), val: body },
                    head: heads,
                })
            }
            Some(Token::Dot) | None => {
                // bare fact: no separator, lhs is the head
                let heads = Self::expr_to_tuples(lhs)?;
                Ok(Rule {
                    body: Closure { ctx: Binding::new(), val: Expr::Unit },
                    head: heads,
                })
            }
            other => Err(format!("expected rule separator or '.', got {:?} at token pos {}", other, self.pos)),
        }
    }

    // -- Program parser -------------------------------------------------------

    fn prog(&mut self) -> PResult<Vec<Rule>> {
        let mut rules = Vec::new();
        loop {
            if self.pos >= self.tokens.len() {
                break;
            }
            let rule = self.rule()?;
            self.expect(&Token::Dot)?;
            rules.push(rule);
        }
        Ok(rules)
    }
}

// -- Public API ---------------------------------------------------------------

/// Strip comments (text from ';' to end of line)
fn lex_comments(input: &str) -> String {
    let mut out = Vec::new();
    for line in input.lines() {
        if line.trim() == "#exit" {
            break;
        }
        if let Some(idx) = line.find(';') {
            out.push(&line[..idx]);
        } else {
            out.push(line);
        }
    }
    out.join("\n")
}

pub fn parse(input: &str, intern: &mut Interner) -> Result<Vec<Rule>, String> {
    let cleaned = lex_comments(input);
    let tokens = lex(&cleaned)?;
    let mut parser = Parser::new(tokens, intern);
    parser.prog()
}
