// structure adapted from [winterfell's](https://github.com/facebook/winterfell/blob/main/math/benches/field.rs)
// and [lambdaworks' bench](https://github.com/lambdaclass/lambdaworks/blob/main/math/benches/fields/u64_goldilocks.rs)
use ark_ff::Field;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

use shitty_ff::goldilocks::Goldilocks;

fn bench_fields(c: &mut Criterion) {
    bench_ops::<Goldilocks>(c, "goldilocks");
}

fn bench_ops<F: Field>(c: &mut Criterion, name: &str) {
    let mut bench_group = c.benchmark_group(format!("bench_{}", name));

    let input: Vec<Vec<(F, F)>> = [1, 10, 100, 1000, 10000, 100000, 1000000]
        .into_iter()
        .map(rand_field_elements)
        .collect::<Vec<_>>();

    for i in input.clone().into_iter() {
        bench_group.bench_with_input(format!("{}_mul_{}", name, i.len()), &i, |b, i| {
            b.iter(|| {
                for (x, y) in i {
                    black_box(*black_box(x) * black_box(y));
                }
            });
        });
    }

    for i in input.clone().into_iter() {
        bench_group.bench_with_input(format!("{}_add_{}", name, i.len()), &i, |b, i| {
            b.iter(|| {
                for (x, y) in i {
                    black_box(*black_box(x) + black_box(y));
                }
            });
        });
    }

    for i in input.clone().into_iter() {
        bench_group.bench_with_input(format!("{}_sub_{}", name, i.len()), &i, |b, i| {
            b.iter(|| {
                for (x, y) in i {
                    black_box(*black_box(x) - black_box(y));
                }
            });
        });
    }

    for i in input.clone().into_iter() {
        bench_group.bench_with_input(format!("{}_inv_{}", name, i.len()), &i, |b, i| {
            b.iter(|| {
                for (x, _) in i {
                    black_box(black_box(x).inverse().unwrap());
                }
            });
        });
    }

    for i in input.clone().into_iter() {
        bench_group.bench_with_input(format!("{}_square_{}", name, i.len()), &i, |b, i| {
            b.iter(|| {
                for (x, _) in i {
                    black_box(black_box(x).square());
                }
            });
        });
    }

    for i in input.clone().into_iter() {
        bench_group.bench_with_input(format!("{}_div_{}", name, i.len()), &i, |b, i| {
            b.iter(|| {
                for (x, y) in i {
                    black_box(*black_box(x) / black_box(y));
                }
            });
        });
    }
}

fn rand_field_elements<F: Field>(num: usize) -> Vec<(F, F)> {
    let mut rng = ark_std::rand::thread_rng();
    let mut result = Vec::with_capacity(num);
    for _ in 0..num {
        result.push((F::rand(&mut rng), F::rand(&mut rng)));
    }

    result
}

criterion_main!(bench);
criterion_group!(bench, bench_fields);
