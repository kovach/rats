use crate::sym::Interner;
use crate::types::*;
use crate::core::{atom};

// -- Parser state -------------------------------------------------------------

struct Parser<'a> {
    input: &'a str,
    pos: usize,
    intern: &'a mut Interner,
}

type PResult<T> = Result<T, String>;

impl<'a> Parser<'a> {
    fn new(input: &'a str, intern: &'a mut Interner) -> Self {
        Parser { input, pos: 0, intern }
    }

    fn remaining(&self) -> &str {
        &self.input[self.pos..]
    }

    fn peek(&self) -> Option<char> {
        self.remaining().chars().next()
    }

    fn advance(&mut self, n: usize) {
        self.pos += n;
    }

    fn char_match(&mut self, f: impl Fn(char) -> bool, desc: &str) -> PResult<char> {
        match self.peek() {
            Some(c) if f(c) => {
                self.advance(c.len_utf8());
                Ok(c)
            }
            _ => Err(format!("[expected: '{}'] at pos {}", desc, self.pos)),
        }
    }

    fn char_exact(&mut self, c: char) -> PResult<char> {
        self.char_match(|ch| ch == c, &c.to_string())
    }

    fn string_exact(&mut self, s: &str) -> PResult<()> {
        if self.remaining().starts_with(s) {
            self.advance(s.len());
            Ok(())
        } else {
            Err(format!("expected '{}' at pos {}", s, self.pos))
        }
    }

    fn ws(&mut self) {
        while let Some(c) = self.peek() {
            if c == ' ' || c == '\n' || c == '\t' {
                self.advance(c.len_utf8());
            } else {
                break;
            }
        }
    }

    fn ws1(&mut self) -> PResult<()> {
        let start = self.pos;
        self.ws();
        if self.pos == start {
            Err(format!("expected whitespace at pos {}", self.pos))
        } else {
            Ok(())
        }
    }

    fn is_id_char(c: char) -> bool {
        c.is_alphanumeric() || c == '-' || c == '/' || c == '_' || c == '\''
    }

    fn predicate(&mut self) -> PResult<String> {
        let first = self.char_match(|c| c.is_lowercase() || c == '#', "lowercase or #")?;
        let mut s = String::new();
        s.push(first);
        while let Some(c) = self.peek() {
            if Self::is_id_char(c) {
                s.push(c);
                self.advance(c.len_utf8());
            } else {
                break;
            }
        }
        Ok(s)
    }

    fn variable(&mut self) -> PResult<String> {
        let first = self.peek().ok_or("expected variable".to_string())?;
        if first.is_uppercase() {
            self.advance(first.len_utf8());
            let mut s = String::new();
            s.push(first);
            while let Some(c) = self.peek() {
                if Self::is_id_char(c) {
                    s.push(c);
                    self.advance(c.len_utf8());
                } else {
                    break;
                }
            }
            Ok(s)
        } else if first == '_' {
            self.advance(first.len_utf8());
            let mut s = String::from("_");
            // _var requires at least one more char (many1 idChar)
            let c = self.char_match(Self::is_id_char, "id char after _")?;
            s.push(c);
            while let Some(c) = self.peek() {
                if Self::is_id_char(c) {
                    s.push(c);
                    self.advance(c.len_utf8());
                } else {
                    break;
                }
            }
            Ok(s)
        } else {
            Err(format!("expected variable at pos {}", self.pos))
        }
    }

    fn nat(&mut self) -> PResult<i32> {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(c);
                self.advance(c.len_utf8());
            } else {
                break;
            }
        }
        if s.is_empty() {
            Err(format!("expected number at pos {}", self.pos))
        } else {
            s.parse::<i32>().map_err(|e| e.to_string())
        }
    }

    fn string_lit(&mut self) -> PResult<String> {
        self.char_exact('"')?;
        let mut s = String::new();
        loop {
            match self.peek() {
                Some('"') => {
                    self.advance(1);
                    return Ok(s);
                }
                Some(c) => {
                    s.push(c);
                    self.advance(c.len_utf8());
                }
                None => return Err("unterminated string".to_string()),
            }
        }
    }

    fn parens<T>(&mut self, f: impl FnOnce(&mut Self) -> PResult<T>) -> PResult<T> {
        self.char_exact('(')?;
        self.ws();
        let v = f(self)?;
        self.ws();
        self.char_exact(')')?;
        Ok(v)
    }

    fn comma_sep<T>(&mut self, f: impl Fn(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        let mut results = Vec::new();
        match f(self) {
            Ok(v) => results.push(v),
            Err(_) => return Ok(results),
        }
        loop {
            let saved = self.pos;
            if self.char_exact(',').is_err() {
                break;
            }
            self.ws();
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

    fn ws_sep<T>(&mut self, f: impl Fn(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        let mut results = Vec::new();
        match f(self) {
            Ok(v) => results.push(v),
            Err(_) => return Ok(results),
        }
        loop {
            let saved = self.pos;
            if self.ws1().is_err() {
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

    // -- Term parser ----------------------------------------------------------

    fn term(&mut self) -> PResult<ATerm> {
        // app <|> v <|> p <|> b <|> n <|> str
        // app = TermApp <$> predicate <*> parens (commaSep term)
        // Try app first (predicate followed by parens), then fall back to pred
        let saved = self.pos;

        // Try app: predicate + parens
        if let Ok(name) = self.predicate() {
            let saved2 = self.pos;
            if let Ok(args) = self.parens(|p| p.comma_sep(|p| p.term())) {
                let sym = self.intern.intern(&name);
                return Ok(aapp(Name::Sym(sym), args));
            }
            // It was just a predicate, not an app
            self.pos = saved2;
            if name.starts_with('#') {
                return Ok(apred(Name::Str(name)));
                // return Ok(apred(Name::Str(String::from(&name[1..]))));
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

        // Try blank (just '_' with no following id chars)
        if let Some('_') = self.peek() {
            // Check it's not a _var (which would be a variable)
            let saved = self.pos;
            self.advance(1);
            match self.peek() {
                Some(c) if Self::is_id_char(c) => {
                    // It's a _var, backtrack and parse as variable
                    self.pos = saved;
                    let v = self.variable()?;
                    let sym = self.intern.intern(&v);
                    return Ok(avar(Name::Sym(sym)));
                }
                _ => return Ok(ablank()),
            }
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

        Err(format!("expected term at pos {}", self.pos))
    }

    // -- Tuple parser ---------------------------------------------------------

    fn tuple(&mut self) -> PResult<Tuple> {
        let terms = self.ws_sep(|p| p.term())?;
        Ok(terms.into_iter().collect())
    }

    // -- Expr parser ----------------------------------------------------------

    fn expr(&mut self) -> PResult<Expr> {
        // simplify <$> joins' <$> commaSep leaf
        let leaves = self.comma_sep(|p| p.expr_leaf())?;
        let e = leaves.into_iter().fold(Expr::Unit, |acc, leaf| join(acc, leaf));
        Ok(e)
    }

    fn expr_leaf(&mut self) -> PResult<Expr> {
        // neg <|> bind <|> tup
        let saved = self.pos;

        // Try neg: '!' followed by terms
        if self.char_exact('!').is_ok() {
            let terms = self.ws_sep(|p| p.term())?;
            let tuple: Tuple = terms.into_iter().collect();
            return Ok(Expr::NegAtom(tuple));
        }
        self.pos = saved;

        // Try bind: term '=' term
        // Need to try this carefully - the '=' must be there
        let saved = self.pos;
        if let Ok(lhs) = self.term() {
            let saved2 = self.pos;
            self.ws();
            if self.char_exact('=').is_ok() {
                self.ws();
                let rhs = self.term()?;
                return Ok(Expr::Bind(lhs, rhs));
            }
            self.pos = saved2;

            // It was a tup start — put lhs back and parse as tup
            self.pos = saved;
        } else {
            self.pos = saved;
        }

        // Try tup: ws_sep term → atom
        let terms = self.ws_sep(|p| p.term())?;
        let tuple: Tuple = terms.into_iter().collect();
        Ok(atom(tuple))
    }

    // -- Rule parser ----------------------------------------------------------

    fn rule(&mut self) -> PResult<Rule> {
        let body = self.expr()?;
        self.ws();
        // "--" followed by optional '-'s
        self.string_exact("--")?;
        while self.char_exact('-').is_ok() {}
        self.ws();
        let heads = self.comma_sep(|p| p.tuple())?;
        Ok(Rule {
            body: Closure { ctx: Binding::new(), val: body },
            head: heads,
        })
    }

    // -- Program parser -------------------------------------------------------

    fn prog(&mut self) -> PResult<Vec<Rule>> {
        let mut rules = Vec::new();
        loop {
            self.ws();
            if self.pos >= self.input.len() {
                break;
            }
            let rule = self.rule()?;
            self.ws();
            self.char_exact('.')?;
            rules.push(rule);
        }
        Ok(rules)
    }
}

// -- Public API ---------------------------------------------------------------

/// Strip comments (lines starting with ';' from comment position onward)
fn lex_comments(input: &str) -> String {
    input
        .lines()
        .map(|line| {
            if let Some(idx) = line.find(';') {
                &line[..idx]
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn parse(input: &str, intern: &mut Interner) -> Result<Vec<Rule>, String> {
    let cleaned = lex_comments(input);
    let mut parser = Parser::new(&cleaned, intern);
    parser.prog()
}
