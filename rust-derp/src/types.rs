use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;
use smallvec::SmallVec;

use crate::sym::{Sym, Interner};

// -- Term ---------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Term {
    Var(Sym),
    Pred(Sym),
    Num(i32),
    Blank,
    App(Sym, Arc<[Term]>),
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

pub type Tuple = SmallVec<[Term; 6]>;

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
        let pred = match &tuple[0] {
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
        let pred = match &tuple[0] {
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
                full.push(Term::Pred(*pred));
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

/// A sorted association list from Sym -> Term, kept sorted by Sym for
/// binary-search lookup. Inline for up to 8 entries.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Binding {
    pub entries: SmallVec<[(Sym, Term); 8]>,
}

impl Binding {
    pub fn new() -> Self {
        Binding {
            entries: SmallVec::new(),
        }
    }

    pub fn from_list(pairs: &[(Sym, Term)]) -> Self {
        let mut b = Binding::new();
        for (k, v) in pairs {
            b.insert_sorted(*k, v.clone());
        }
        b
    }

    fn insert_sorted(&mut self, key: Sym, val: Term) {
        match self.entries.binary_search_by_key(&key, |(k, _)| *k) {
            Ok(idx) => self.entries[idx] = (key, val),
            Err(idx) => self.entries.insert(idx, (key, val)),
        }
    }

    pub fn lookup(&self, key: Sym) -> Option<&Term> {
        self.entries
            .binary_search_by_key(&key, |(k, _)| *k)
            .ok()
            .map(|idx| &self.entries[idx].1)
    }

    pub fn extend(&self, key: Sym, val: Term) -> Binding {
        let mut b = self.clone();
        b.insert_sorted(key, val);
        b
    }

    /// Try to extend: if key already exists, check val == existing.
    pub fn try_extend(&self, key: Sym, val: &Term) -> Option<Binding> {
        if let Some(existing) = self.lookup(key) {
            if existing == val {
                Some(self.clone())
            } else {
                None
            }
        } else {
            Some(self.extend(key, val.clone()))
        }
    }

    /// Merge another binding into this one, failing if any key conflicts.
    pub fn merge(&self, other: &Binding) -> Option<Binding> {
        let mut result = self.clone();
        for (k, v) in &other.entries {
            result = result.try_extend(*k, v)?;
        }
        Some(result)
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
    Bind(Term, Term),
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
