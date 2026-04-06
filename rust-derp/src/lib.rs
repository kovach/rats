pub mod sym;
pub mod types;
pub mod core;
pub mod parse;

pub fn eval(input: &str, reorder: bool) -> (types::Tuples, types::TermTable, sym::Interner, core::EvalStats) {
    use std::collections::HashSet;
    let mut intern = sym::Interner::new();
    let rules = parse::parse(input, &mut intern).expect("parse error");
    let lt_sym = intern.intern("lt");
    let eq_sym = intern.intern("eq");
    let index_specs = vec![(lt_sym, 0), (lt_sym, 1), (eq_sym, 0), (eq_sym, 1)];
    let (result, table, stats) = core::iter_rules(HashSet::new(), rules, &intern, reorder, index_specs);
    (result, table, intern, stats)
}
