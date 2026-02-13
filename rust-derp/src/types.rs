use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;
use smallvec::SmallVec;

use crate::sym::{Sym, Interner};

// -- Term ---------------------------------------------------------------------

pub type ATerm = Rc<Term>;

pub fn avar(s: Sym) -> ATerm { Rc::new(Term::Var(s)) }
pub fn apred(s: Sym) -> ATerm { Rc::new(Term::Pred(s)) }
pub fn anum(n: i32) -> ATerm { Rc::new(Term::Num(n)) }
pub fn ablank() -> ATerm { Rc::new(Term::Blank) }
pub fn astr(s: Sym) -> ATerm { Rc::new(Term::Str(s)) }
pub fn aapp(cons: Sym, args: Vec<ATerm>) -> ATerm { Rc::new(Term::App(cons, args)) }
pub fn aterm_ptr_eq(a: &ATerm, b: &ATerm) -> bool { Rc::ptr_eq(a, b) }

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Term {
    Var(Sym),
    Pred(Sym),
    Num(i32),
    Blank,
    App(Sym, Vec<ATerm>),
    Str(Sym),
}

impl Term {
    pub fn pp(&self, i: &Interner) -> String {
        match self {
            Term::Var(s) => i.resolve(*s).to_owned(),
            Term::Pred(s) => i.resolve(*s).to_owned(),
            Term::Num(n) => n.to_string(),
            Term::Blank => "_".to_owned(),
            Term::App(name, args) => {
                let arg_strs: Vec<String> = args.iter().map(|t| t.pp(i)).collect();
                format!("{}({})", i.resolve(*name), arg_strs.join(", "))
            }
            Term::Str(s) => format!("\"{}\"", i.resolve(*s)),
        }
    }
}

// -- Tuple --------------------------------------------------------------------

pub type Tuple = SmallVec<[ATerm; 6]>;

pub fn pp_tuple(t: &Tuple, i: &Interner) -> String {
    t.iter().map(|term| term.pp(i)).collect::<Vec<_>>().join(" ")
}

// -- Tuples (the relation store) ----------------------------------------------

#[derive(Clone, Debug)]
pub struct Tuples {
    pub relations: HashMap<Sym, HashSet<Tuple>>,
}

impl Tuples {
    pub fn new() -> Self {
        Tuples {
            relations: HashMap::new(),
        }
    }

    /// Insert a tuple (pred : rest). Returns true if the tuple was new.
    pub fn insert_tuple(&mut self, tuple: &Tuple) -> bool {
        let pred = match tuple[0].as_ref() {
            Term::Pred(p) => *p,
            _ => panic!("tuple must start with a Pred"),
        };
        let rest: Tuple = tuple[1..].into();
        self.relations
            .entry(pred)
            .or_insert_with(HashSet::new)
            .insert(rest)
    }

    /// Insert with pred already separated.
    pub fn insert(&mut self, pred: Sym, rest: Tuple) -> bool {
        self.relations
            .entry(pred)
            .or_insert_with(HashSet::new)
            .insert(rest)
    }

    pub fn contains_tuple(&self, tuple: &Tuple) -> bool {
        let pred = match tuple[0].as_ref() {
            Term::Pred(p) => *p,
            _ => panic!("tuple must start with a Pred"),
        };
        let rest: Tuple = tuple[1..].into();
        self.relations
            .get(&pred)
            .map_or(false, |set| set.contains(&rest))
    }

    pub fn contains(&self, pred: Sym, rest: &Tuple) -> bool {
        self.relations
            .get(&pred)
            .map_or(false, |set| set.contains(rest))
    }

    pub fn lookup(&self, pred: Sym) -> impl Iterator<Item = &Tuple> {
        self.relations
            .get(&pred)
            .into_iter()
            .flat_map(|set| set.iter())
    }

    /// Merge other into self (union semantics).
    pub fn union_from(&mut self, other: &Tuples) {
        for (pred, tuples) in &other.relations {
            let entry = self.relations.entry(*pred).or_insert_with(HashSet::new);
            for t in tuples {
                entry.insert(t.clone());
            }
        }
    }

    /// Add a single full tuple (with pred prefix).
    pub fn add_one(&mut self, tuple: &Tuple) {
        self.insert_tuple(tuple);
    }

    pub fn size(&self) -> usize {
        self.relations.values().map(|s| s.len()).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.relations.values().all(|s| s.is_empty())
    }

    pub fn pp(&self, i: &Interner) -> String {
        let mut lines: Vec<String> = Vec::new();
        // Sort by pred name for deterministic output
        let mut preds: Vec<_> = self.relations.iter().collect();
        preds.sort_by_key(|(p, _)| i.resolve(**p));
        for (pred, tuples) in preds {
            let mut sorted_tuples: Vec<_> = tuples.iter().collect();
            sorted_tuples.sort();
            for t in sorted_tuples {
                let mut full: Tuple = SmallVec::new();
                full.push(apred(*pred));
                full.extend(t.iter().cloned());
                lines.push(pp_tuple(&full, i));
            }
        }
        lines.join("\n")
    }
}

// -- Worklist -----------------------------------------------------------------

pub type Worklist = VecDeque<Tuple>;

// -- Binding ------------------------------------------------------------------

/// A sorted association list from Sym -> ATerm, kept sorted by Sym for
/// binary-search lookup. Inline for up to 8 entries.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Binding {
    pub entries: SmallVec<[(Sym, ATerm); 8]>,
    pub stack: SmallVec<[usize; 8]>,
}

impl Binding {
    pub fn new() -> Self {
        Binding {
            entries: SmallVec::new(),
            stack: SmallVec::new(),
        }
    }

    fn insert(&mut self, key: Sym, val: ATerm) {
        self.entries.push((key, val));
    }

    pub fn push(&mut self) {
        self.stack.push(self.entries.len());
    }
    pub fn pop(&mut self) {
        match self.stack.pop() {
            Some(k) => self.entries.truncate(k),
            None => (),
        }
    }

    pub fn lookup(&self, key: Sym) -> Option<&ATerm> {
        for (k, v) in self.entries.iter().rev() {
            if *k == key {
                return Some(v);
            }
        }
        None
    }

    pub fn try_extend(&mut self, key: Sym, val: &ATerm) -> bool {
        match self.lookup(key) {
        // match self.entries.binary_search_by_key(&key, |(k, _)| *k) {
            Some(v) => {
                if v == val {
                    true
                } else {
                    false
                }
            }
            None => {
                self.insert(key, val.clone());
                // self.entries.insert(idx, (key, val.clone()));
                true
            }
        }
    }

    pub fn pp(&self, i: &Interner) -> String {
        self.entries
            .iter()
            .map(|(k, v)| format!("{} {}", i.resolve(*k), v.pp(i)))
            .collect::<Vec<_>>()
            .join(" / ")
    }
}

// -- Expression ---------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Expr {
    Atom(Tuple),
    NegAtom(Tuple),
    Bind(ATerm, ATerm),
    Join(Box<Expr>, Box<Expr>),
    Unit,
}

// -- Closure and Rule ---------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Closure {
    pub ctx: Binding,
    pub val: Expr,
}

pub type CE = Closure;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rule {
    pub body: CE,
    pub head: Vec<Tuple>,
}
