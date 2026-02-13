mod sym;
mod types;
mod core;
mod parse;

use std::collections::HashSet;
use std::env;
use std::fs;
use std::time::{Duration, Instant};

fn run_with_rules(rules: &[types::Rule], intern: &sym::Interner, timeout: Duration) -> Result<types::Tuples, Duration> {
    let initial: HashSet<types::Tuple> = HashSet::new();
    let start = Instant::now();
    // We can't easily interrupt iter_rules, so we just time it
    let result = core::iter_rules(initial, rules, intern);
    let elapsed = start.elapsed();
    if elapsed > timeout {
        Err(elapsed)
    } else {
        Ok(result)
    }
}

fn bisect(rules: &[types::Rule], intern: &sym::Interner, timeout: Duration) {
    eprintln!("bisecting {} rules with {}s timeout", rules.len(), timeout.as_secs());
    for n in 1..=rules.len() {
        let subset = &rules[..n];
        eprint!("rules 1..{}: ", n);
        let start = Instant::now();
        let result = run_with_rules(subset, intern, timeout);
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
    let filename = args.get(1).expect("usage: derp <file.derp> [--bisect]");
    let do_bisect = args.iter().any(|a| a == "--bisect");

    let input = fs::read_to_string(filename).expect("could not read file");

    let mut intern = sym::Interner::new();
    let rules = parse::parse(&input, &mut intern).expect("parse error");

    eprintln!("parsed {} rules", rules.len());

    if do_bisect {
        bisect(&rules, &intern, Duration::from_secs(3));
    } else {
        let initial: HashSet<types::Tuple> = HashSet::new();
        let result = core::iter_rules(initial, &rules, &intern);
        println!("{}", result.to_json(&intern));
        eprintln!("{} tuples", result.size());
    }
}
