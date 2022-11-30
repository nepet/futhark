use criterion::{black_box, criterion_group, criterion_main, Criterion};
use futhark::{Alternative, Restriction};

fn decoding_alternative_benchmark(c: &mut Criterion) {
    let alternatives = black_box("f1=v1|f2!|f3$foobar&f1/v2");

    c.bench_function("alternative decoding", |b| {
        b.iter(|| Alternative::decode(alternatives, false))
    });
}

fn decoding_restriction_benchmark(c: &mut Criterion) {
    let restriction = black_box("f1=v1&f1/v2");

    c.bench_function("restriction decoding", |b| {
        b.iter(|| Restriction::decode(restriction, false))
    });
}

criterion_group!(
    benches,
    decoding_alternative_benchmark,
    decoding_restriction_benchmark
);
criterion_main!(benches);
