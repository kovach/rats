use derp::{sym, types, core, parse};

use std::collections::HashSet;
use std::env;
use std::fs;
use std::time::{Duration, Instant};

fn run_with_rules(rules: &[types::Rule], intern: &sym::Interner, timeout: Duration, reorder: bool) -> Result<types::Tuples, Duration> {
    let initial: HashSet<types::Tuple> = HashSet::new();
    let start = Instant::now();
    // We can't easily interrupt iter_rules, so we just time it
    let (result, _table) = core::iter_rules(initial, rules.to_vec(), intern, reorder);
    let elapsed = start.elapsed();
    if elapsed > timeout {
        Err(elapsed)
    } else {
        Ok(result)
    }
}

fn bisect(rules: &[types::Rule], intern: &sym::Interner, timeout: Duration, reorder: bool) {
    eprintln!("bisecting {} rules with {}s timeout", rules.len(), timeout.as_secs());
    for n in 1..=rules.len() {
        let subset = &rules[..n];
        eprint!("rules 1..{}: ", n);
        let start = Instant::now();
        let result = run_with_rules(subset, intern, timeout, reorder);
        let elapsed = start.elapsed();
        match result {
            Ok(tuples) => {
                eprintln!("ok ({:.2}s, {} tuples)", elapsed.as_secs_f64(), tuples.size());
            }
            Err(elapsed) => {
                eprintln!("TIMEOUT ({:.2}s)", elapsed.as_secs_f64());
                eprintln!("rule {} is the first to cause timeout", n);
                return;
            }
        }
    }
    eprintln!("all rules completed within timeout");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let filename = args.get(1).expect("usage: derp <file.derp> [--bisect] [--reorder]");
    let do_bisect = args.iter().any(|a| a == "--bisect");
    let reorder = args.iter().any(|a| a == "--reorder");

    let input = fs::read_to_string(filename).expect("could not read file");

    let mut intern = sym::Interner::new();
    let rules = parse::parse(&input, &mut intern).expect("parse error");

    eprintln!("parsed {} rules", rules.len());

    if do_bisect {
        bisect(&rules, &intern, Duration::from_secs(3), reorder);
    } else {
        let initial: HashSet<types::Tuple> = HashSet::new();
        let (result, table) = core::iter_rules(initial, rules, &intern, reorder);

        let base = filename.trim_end_matches(".derp");
        let json_path = format!("{}.json", base);
        let derp_path = format!("{}.out.derp", base);

        fs::write(&json_path, result.to_json_with_table(&intern, &table)).expect("could not write json");
        fs::write(&derp_path, result.pp_derp_with_table(&intern, &table)).expect("could not write derp");

        eprintln!("{} tuples, wrote {} and {}", result.size(), json_path, derp_path);
    }
}
