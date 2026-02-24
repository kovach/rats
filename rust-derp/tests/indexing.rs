use std::collections::HashSet;
use derp::{core, parse, sym, types::anum};

#[test]
fn test_lt_index_populated() {
    let src = "-- lt 1 2. -- lt 1 3. -- lt 2 3.";
    let mut intern = sym::Interner::new();
    let rules = parse::parse(src, &mut intern).expect("parse");
    let lt_sym = intern.intern("lt");
    let specs = vec![(lt_sym, 0), (lt_sym, 1)];
    let (tuples, ..) = core::iter_rules(HashSet::new(), rules, &intern, false, specs);

    // Main relation has 3 tuples
    assert_eq!(tuples.relations[&lt_sym].len(), 3);

    // Col-0 index: value 1 → 2 tuples; value 2 → 1 tuple
    let c0 = &tuples.indices[&(lt_sym, 0)];
    assert_eq!(c0[&anum(1)].len(), 2);
    assert_eq!(c0[&anum(2)].len(), 1);

    // Col-1 index: value 2 → 1 tuple; value 3 → 2 tuples
    let c1 = &tuples.indices[&(lt_sym, 1)];
    assert_eq!(c1[&anum(2)].len(), 1);
    assert_eq!(c1[&anum(3)].len(), 2);
}
