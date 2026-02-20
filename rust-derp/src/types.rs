use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;
use smallvec::SmallVec;
use serde::Serialize;

use crate::sym::{Sym, Interner};

// -- Term ---------------------------------------------------------------------

pub type ATerm = Rc<Term>;

pub fn avar(s: Name) -> ATerm { Rc::new(Term::Var(VarOp::Name(s))) }
pub fn apred(s: Name) -> ATerm { Rc::new(Term::Pred(s)) }
pub fn anum(n: i32) -> ATerm { Rc::new(Term::Num(n)) }
pub fn ablank() -> ATerm { Rc::new(Term::Blank) }
pub fn astr(s: Name) -> ATerm { Rc::new(Term::Str(s)) }
pub fn aapp(cons: Name, args: Vec<ATerm>) -> ATerm { Rc::new(Term::App(cons, args)) }
pub fn aid(id: u32) -> ATerm { Rc::new(Term::Id(id)) }
pub fn aterm_ptr_eq(a: &ATerm, b: &ATerm) -> bool { Rc::ptr_eq(a, b) }

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize)]
#[serde(untagged)]
pub enum Name {
    #[serde(skip)]
    Sym(Sym),
    Str(String),
}

impl Name {
    pub fn resolve<'a>(&'a self, i: &'a Interner) -> &'a str {
        match self {
            Name::Sym(s) => i.resolve(*s),
            Name::Str(s) => s.as_str(),
        }
    }

    pub fn as_sym(&self) -> Sym {
        match self {
            Name::Sym(s) => *s,
            Name::Str(_) => panic!("Name::as_sym called on Str"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum VarOp {
    Name(Name),  // uncompiled variable
    Set(u16),    // first occurrence — write to slot unconditionally
    Check(u16),  // later occurrence — compare slot value for equality
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Term {
    Var(VarOp),
    Pred(Name),
    Num(i32),
    Blank,
    App(Name, Vec<ATerm>),
    Str(Name),
    Id(u32),
}

impl Serialize for Term {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;
        match self {
            Term::Var(VarOp::Name(name)) => {
                let mut map = serializer.serialize_map(Some(2))?;
                map.serialize_entry("tag", "var")?;
                map.serialize_entry("name", name)?;
                map.end()
            }
            Term::Var(op) => panic!("cannot serialize compiled VarOp: {:?}", op),
            Term::Pred(name) => {
                let mut map = serializer.serialize_map(Some(2))?;
                map.serialize_entry("tag", "pred")?;
                map.serialize_entry("name", name)?;
                map.end()
            }
            Term::Num(n) => {
                let mut map = serializer.serialize_map(Some(2))?;
                map.serialize_entry("tag", "num")?;
                map.serialize_entry("value", n)?;
                map.end()
            }
            Term::Blank => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("tag", "blank")?;
                map.end()
            }
            Term::App(name, args) => {
                let mut map = serializer.serialize_map(Some(3))?;
                map.serialize_entry("tag", "app")?;
                map.serialize_entry("name", name)?;
                map.serialize_entry("args", args)?;
                map.end()
            }
            Term::Str(value) => {
                let mut map = serializer.serialize_map(Some(2))?;
                map.serialize_entry("tag", "string")?;
                map.serialize_entry("value", value)?;
                map.end()
            }
            Term::Id(n) => {
                let mut map = serializer.serialize_map(Some(2))?;
                map.serialize_entry("tag", "id")?;
                map.serialize_entry("id", n)?;
                map.end()
            }
        }
    }
}

impl Term {
    pub fn pp(&self, i: &Interner) -> String {
        match self {
            Term::Var(VarOp::Name(s)) => s.resolve(i).to_owned(),
            Term::Var(VarOp::Set(n)) => format!("${}", n),
            Term::Var(VarOp::Check(n)) => format!("${}?", n),
            Term::Pred(s) => s.resolve(i).to_owned(),
            Term::Num(n) => n.to_string(),
            Term::Blank => "_".to_owned(),
            Term::App(name, args) => {
                let arg_strs: Vec<String> = args.iter().map(|t| t.pp(i)).collect();
                format!("{}({})", name.resolve(i), arg_strs.join(", "))
            }
            Term::Str(s) => format!("\"{}\"", s.resolve(i)),
            Term::Id(n) => format!("#{}", n),
        }
    }

    /// Resolve all Name::Sym → Name::Str using the interner.
    pub fn resolve_names(&self, i: &Interner) -> Term {
        match self {
            Term::Var(VarOp::Name(s)) => Term::Var(VarOp::Name(Name::Str(s.resolve(i).to_owned()))),
            Term::Var(op) => panic!("cannot resolve_names on compiled VarOp: {:?}", op),
            Term::Pred(s) => Term::Pred(Name::Str(s.resolve(i).to_owned())),
            Term::Num(_) | Term::Blank | Term::Id(_) => self.clone(),
            Term::App(name, args) => {
                let new_args = args.iter().map(|a| Rc::new(a.resolve_names(i))).collect();
                Term::App(Name::Str(name.resolve(i).to_owned()), new_args)
            }
            Term::Str(s) => Term::Str(Name::Str(s.resolve(i).to_owned())),
        }
    }

    /// Intern all Name::Str → Name::Sym using the interner.
    pub fn intern_names(&self, i: &mut Interner) -> Term {
        match self {
            Term::Var(VarOp::Name(Name::Str(s))) => Term::Var(VarOp::Name(Name::Sym(i.intern(s)))),
            Term::Var(VarOp::Name(Name::Sym(_))) => self.clone(),
            Term::Var(op) => panic!("cannot intern_names on compiled VarOp: {:?}", op),
            Term::Pred(Name::Str(s)) => Term::Pred(Name::Sym(i.intern(s))),
            Term::Pred(Name::Sym(_)) => self.clone(),
            Term::Num(_) | Term::Blank | Term::Id(_) => self.clone(),
            Term::App(name, args) => {
                let new_name = match name {
                    Name::Str(s) => Name::Sym(i.intern(s)),
                    n @ Name::Sym(_) => n.clone(),
                };
                let new_args = args.iter().map(|a| Rc::new(a.intern_names(i))).collect();
                Term::App(new_name, new_args)
            }
            Term::Str(Name::Str(s)) => Term::Str(Name::Sym(i.intern(s))),
            Term::Str(Name::Sym(_)) => self.clone(),
        }
    }

    pub fn vars(&self) -> Vec<Name> {
        match self {
            Term::Var(VarOp::Name(n)) => vec![n.clone()],
            Term::Var(_) => panic!("vars() called on compiled term"),
            Term::App(_, args) => args.iter().flat_map(|a| a.vars()).collect(),
            Term::Pred(_) | Term::Num(_) | Term::Blank | Term::Str(_) | Term::Id(_) => vec![],
        }
    }
}

// -- TermTable ----------------------------------------------------------------

/// Interning table for Term::App values. Stores flat Apps (args are non-App)
/// and returns Term::Id handles for O(1) hashing.
#[derive(Debug)]
pub struct TermTable {
    map: HashMap<(Name, Vec<ATerm>), u32>,
    pub vec: Vec<ATerm>,  // index == id; entries are always Term::App
}

impl TermTable {
    pub fn new() -> Self {
        TermTable {
            map: HashMap::new(),
            vec: Vec::new(),
        }
    }

    /// Intern a Term::App with the given constructor and (already-flat) args.
    /// Returns Term::Id(id) for deduplication.
    pub fn store(&mut self, cons: Name, args: Vec<ATerm>) -> ATerm {
        let key = (cons, args);
        if let Some(&id) = self.map.get(&key) {
            return aid(id);
        }
        let id = self.vec.len() as u32;
        self.vec.push(aapp(key.0.clone(), key.1.clone()));
        self.map.insert(key, id);
        aid(id)
    }

    pub fn get(&self, id: u32) -> &ATerm {
        &self.vec[id as usize]
    }

    pub fn entries(&self) -> impl Iterator<Item = &ATerm> {
        self.vec.iter()
    }
}

// -- Tuple --------------------------------------------------------------------

pub type Tuple = SmallVec<[ATerm; 6]>;

pub fn unit_tuple() -> Tuple { smallvec::smallvec![apred(Name::Str("".to_string()))] }

pub fn pp_tuple(t: &Tuple, i: &Interner) -> String {
    t.iter().map(|term| term.pp(i)).collect::<Vec<_>>().join(" ")
}

pub fn tuple_vars(t: &Tuple) -> Vec<Name> {
    t.iter().flat_map(|term| term.vars()).collect()
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
            Term::Pred(p) => p.as_sym(),
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
            Term::Pred(p) => p.as_sym(),
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

    pub fn lookup(&self, pred: &Sym) -> impl Iterator<Item = &Tuple> {
        self.relations
            .get(pred)
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
                full.push(apred(Name::Sym(*pred)));
                full.extend(t.iter().cloned());
                lines.push(pp_tuple(&full, i));
            }
        }
        lines.join("\n")
    }

    pub fn pp_derp(&self, i: &Interner) -> String {
        let mut parts: Vec<String> = Vec::new();
        let mut preds: Vec<_> = self.relations.iter().collect();
        preds.sort_by_key(|(p, _)| i.resolve(**p));
        for (pred, tuples) in preds {
            let mut sorted_tuples: Vec<_> = tuples.iter().collect();
            sorted_tuples.sort();
            for t in sorted_tuples {
                let mut full: Tuple = SmallVec::new();
                full.push(apred(Name::Sym(*pred)));
                full.extend(t.iter().cloned());
                parts.push(pp_tuple(&full, i));
            }
        }
        format!("-- {}.", parts.join(",\n   "))
    }

    pub fn to_json(&self, i: &Interner) -> String {
        use serde_json::{Map, Value};
        let mut map = Map::new();
        let mut preds: Vec<_> = self.relations.iter().collect();
        preds.sort_by_key(|(p, _)| i.resolve(**p));
        for (pred, tuples) in preds {
            let mut sorted_tuples: Vec<_> = tuples.iter().collect();
            sorted_tuples.sort();
            let json_tuples: Vec<Value> = sorted_tuples.iter().map(|t| {
                let terms: Vec<Value> = t.iter().map(|term| {
                    let resolved = term.resolve_names(i);
                    serde_json::to_value(&resolved).expect("serialize term")
                }).collect();
                Value::Array(terms)
            }).collect();
            map.insert(i.resolve(*pred).to_owned(), Value::Array(json_tuples));
        }
        serde_json::to_string(&map).expect("serialize tuples")
    }
}

// -- Worklist -----------------------------------------------------------------

pub type Worklist = VecDeque<Tuple>;

// -- Binding ------------------------------------------------------------------

/// A sorted association list from Sym -> ATerm, kept sorted by Sym for
/// binary-search lookup. Inline for up to 8 entries.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Binding {
    pub entries: Vec<(Sym, ATerm)>,
}

#[macro_export]
macro_rules! reset_binding {
    ($x:expr, $fn:expr) => {
        let tmp = $x.entries.len();
        $fn;
        $x.entries.truncate(tmp);
    };
}

impl Binding {
    pub fn new() -> Self {
        Binding {
            entries: Vec::with_capacity(16),
        }
    }

    fn insert(&mut self, key: Sym, val: ATerm) {
        self.entries.push((key, val));
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
            Some(v) => {
                if v == val {
                    true
                } else {
                    false
                }
            }
            None => {
                self.insert(key, val.clone());
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

    pub fn bound_vars(&self) -> Vec<Name> {
        self.entries.iter().map(|(k, _)| Name::Sym(*k)).collect()
    }
}

pub fn count_shared<T: PartialEq>(a: &[T], b: &[T]) -> usize {
    a.iter().filter(|x| b.contains(x)).count()
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

pub fn join(a: Expr, b: Expr) -> Expr {
    match (&a, &b) {
        (Expr::Unit, _) => b,
        (_, Expr::Unit) => a,
        _ => Expr::Join(Box::new(a), Box::new(b)),
    }
}

impl Expr {
    pub fn flatten(self: &Expr) -> Vec<Expr> {
        match self {
            Expr::Join(a, b) => {
                let mut v = a.flatten();
                v.extend(b.flatten());
                v
            }
            Expr::Unit => vec![],
            other => vec![other.clone()],
        }
    }
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

// -- Precomputed specialization -----------------------------------------------

/// One way to extract atom(s) matching a predicate from a rule's Join tree.
/// `pats` are the atom patterns to unify against the incoming tuple.
/// `remaining` is the expression left after removing those atoms.
#[derive(Clone, Debug)]
pub struct SpecEntry {
    pub pats: Vec<Tuple>,            // compiled atom patterns (each without the pred)
    pub remaining: Expr,             // compiled remaining expression
    pub head: Vec<Tuple>,            // compiled head tuples for substitution
    pub num_slots: u16,              // total number of variable slots
}

#[derive(Clone, Debug)]
pub struct SpecializedRule {
    pub entries: Vec<SpecEntry>,
}
