use std::collections::HashSet;
use derp::{core, parse, sym, types::Term};

fn run(src: &str) -> (derp::types::Tuples, derp::types::TermTable) {
    let mut intern = sym::Interner::new();
    let rules = parse::parse(src, &mut intern).expect("parse");
    core::iter_rules(HashSet::new(), rules, &intern, false)
}

/// Invariant 1: no Term::App appears in any output Tuple.
#[test]
fn test_no_app_in_tuples() {
    let (tuples, _table) = run("-- foo pair(1, 2).");
    for (_pred, set) in &tuples.relations {
        for tuple in set {
            for term in tuple {
                assert!(
                    !matches!(term.as_ref(), Term::App(_, _)),
                    "found Term::App in output tuple: {:?}", term
                );
            }
        }
    }
}

/// Invariant 2: every TermTable entry has only non-App args (flat).
#[test]
fn test_table_keys_are_flat() {
    let (_tuples, table) = run("-- foo bar(pair(triple(1,2),3)).");
    for entry in table.entries() {
        if let Term::App(_, args) = entry.as_ref() {
            for arg in args {
                assert!(
                    !matches!(arg.as_ref(), Term::App(_, _)),
                    "found Term::App in TermTable entry args: {:?}", arg
                );
            }
        }
    }
}
