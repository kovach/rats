use std::collections::HashSet;
use derp::{core, parse, sym};

#[test]
fn ttt_produces_4636_tuples() {
    let input = include_str!("data/ttt.derp");
    let mut intern = sym::Interner::new();
    let rules = parse::parse(input, &mut intern).expect("parse");
    let (tuples, _table) = core::iter_rules(HashSet::new(), rules, &intern, false);
    assert_eq!(tuples.size(), 4636);
}
