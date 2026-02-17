use criterion::{criterion_group, criterion_main, Criterion };
use std::collections::HashSet;

fn bench_file(c: &mut Criterion, name: &str, path: &str) {
    let input = std::fs::read_to_string(path).expect(&format!("read file: {}", path));
    c.bench_function(name, |b| {
        b.iter(|| {
            let mut intern = derp::sym::Interner::new();
            let rules = derp::parse::parse(&input, &mut intern).expect("parse");
            let initial = HashSet::new();
            derp::core::iter_rules(initial, &rules, &intern)
        });
    });
}

fn benchmarks(c: &mut Criterion) {
    bench_file(c, "test_simple", "benches/data/test_simple.derp");
    bench_file(c, "test_negation", "benches/data/test_negation.derp");
}

fn bench_out(c: &mut Criterion) {
    let input = std::fs::read_to_string("benches/data/out.derp").expect("read file: out.derp");
    let mut group = c.benchmark_group("out");
    group.sample_size(10);
    group.bench_function("out", |b| {
        b.iter(|| {
            let mut intern = derp::sym::Interner::new();
            let rules = derp::parse::parse(&input, &mut intern).expect("parse");
            let initial = HashSet::new();
            derp::core::iter_rules(initial, &rules, &intern)
        });
    });
    group.finish();
}

criterion_group!(benches, benchmarks, bench_out);
criterion_main!(benches);
