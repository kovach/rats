use std::collections::{BTreeMap, BTreeSet};

type Canonical = BTreeMap<String, BTreeSet<Vec<String>>>;

fn eval_canonical(src: &str) -> Canonical {
    let (tuples, table, intern, _) = derp::eval(src, false);
    let mut result: Canonical = BTreeMap::new();
    for (pred_sym, tset) in &tuples.relations {
        let pred_name = intern.resolve(*pred_sym).to_string();
        let rows: BTreeSet<Vec<String>> = tset.iter()
            .map(|tuple| tuple.iter()
                .map(|t| t.expand_ids(&table).pp(&intern))
                .collect())
            .collect();
        result.insert(pred_name, rows);
    }
    result
}

fn run_pair(name: &str) {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/tests");
    let filename = name.replace('_', "-");
    let input = std::fs::read_to_string(dir.join(format!("{}.derp", filename)))
        .unwrap_or_else(|e| panic!("could not read {}.derp: {}", name, e));
    let expected_src = std::fs::read_to_string(dir.join(format!("{}.expected.derp", filename)))
        .unwrap_or_else(|e| panic!("could not read {}.expected.derp: {}", name, e));

    let got = eval_canonical(&input);
    let expected = eval_canonical(&expected_src);

    assert_eq!(got, expected, "mismatch for test '{}'", name);
}

macro_rules! golden {
    ($($name:ident),* $(,)?) => {
        $(
            #[test]
            fn $name() { run_pair(stringify!($name)); }
        )*
    }
}

golden!(
    add,
    better_path_1,
    game_1,
    game_2,
    game_3,
    init_1,
    loop_miscount_1,
    loop_miscount_2,
    loop_miscount_3,
    t1,
    terms_1,
    total_1,
);
