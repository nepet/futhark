use criterion::{black_box, criterion_group, criterion_main, Criterion};
use runeauth::add_padding;

fn inplace_padding_benchmark(c: &mut Criterion) {
    let mut arr = black_box(vec![1u8; 27]);

    c.bench_function("alternative decoding", |b| {
        b.iter(|| {
            add_padding(arr.len(), &mut arr);
        })
    });
}

criterion_group!(benches, inplace_padding_benchmark);
criterion_main!(benches);
