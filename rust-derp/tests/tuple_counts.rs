use std::collections::HashSet;
use derp::{core, parse, sym};

#[test]
fn ttt_produces_4636_tuples() {
    let input = include_str!("data/ttt.derp");
    let mut intern = sym::Interner::new();
    let rules = parse::parse(input, &mut intern).expect("parse");
    let (tuples, _table, _stats) = core::iter_rules(HashSet::new(), rules, &intern, false, vec![]);
    assert_eq!(tuples.size(), 4636);
}

#[test]
// requires 3 iteration steps
fn neg_test_1() {
    let input = include_str!("data/neg_simple.derp");
    let mut intern = sym::Interner::new();
    let rules = parse::parse(input, &mut intern).expect("parse");
    let (tuples, _table, _stats) = core::iter_rules(HashSet::new(), rules, &intern, false, vec![]);
    assert_eq!(tuples.size(), 21);
}

#[test]
fn neg_ex_test_1() {
    let input = include_str!("data/neg_ex.derp");
    let mut intern = sym::Interner::new();
    let rules = parse::parse(input, &mut intern).expect("parse");
    let (tuples, _table, _stats) = core::iter_rules(HashSet::new(), rules, &intern, false, vec![]);
    assert_eq!(tuples.size(), 6);
}

#[test]
fn neg_circ_test_1() {
    let input = include_str!("data/circle.derp");
    let mut intern = sym::Interner::new();
    let rules = parse::parse(input, &mut intern).expect("parse");
    let (tuples, _table, _stats) = core::iter_rules(HashSet::new(), rules, &intern, false, vec![]);
    assert_eq!(tuples.size(), 1);
}

#[test]
fn arith1() {
    let input = include_str!("data/arith.derp");
    let mut intern = sym::Interner::new();
    let rules = parse::parse(input, &mut intern).expect("parse");
    let (tuples, _table, _stats) = core::iter_rules(HashSet::new(), rules, &intern, false, vec![]);
    assert_eq!(tuples.size(), 3);
}
