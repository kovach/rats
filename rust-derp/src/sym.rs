use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(u32);

pub struct Interner {
    map: HashMap<String, Sym>,
    vec: Vec<String>,
}

impl Interner {
    pub fn new() -> Self {
        Interner {
            map: HashMap::new(),
            vec: Vec::new(),
        }
    }

    pub fn intern(&mut self, s: &str) -> Sym {
        if let Some(&sym) = self.map.get(s) {
            return sym;
        }
        let sym = Sym(self.vec.len() as u32);
        self.vec.push(s.to_owned());
        self.map.insert(s.to_owned(), sym);
        sym
    }

    pub fn resolve(&self, sym: Sym) -> &str {
        &self.vec[sym.0 as usize]
    }
}

impl fmt::Debug for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Sym({})", self.0)
    }
}
