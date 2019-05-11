#[macro_use]
extern crate criterion;

use concurrent_hashmap::hashmap::HashMap;
use core::time::Duration;
use criterion::Criterion;
use rand::seq::SliceRandom;
use rand::thread_rng;
use std::sync::Arc;
use std::thread;

type Key = i32;
type Value = Key;
type Inputs = Vec<(Key, Value)>;

fn random_operations_benchmark(c: &mut Criterion) {
    let mut n = 100;
    while n <= 1_000_000 {
        let title = format!("{} random operations", n);
        let inputs = new_random_array(n);
        c.bench_function(&title, move |b| {
            b.iter_with_setup(|| inputs.to_vec(), |inputs| random_operations(inputs));
        });
        n *= 10;
    }
}

fn random_operations(inputs: Inputs) {
    let m = Arc::new(HashMap::new());
    let inputs = Arc::new(inputs);

    let threads_num = num_cpus::get();
    let mut threads = Vec::new();
    for _ in 0..threads_num {
        let m = m.clone();
        let inputs = inputs.clone();
        threads.push(thread::spawn(move || {
            inputs.iter().for_each(|(key, value)| {
                if key % 2 == 0 {
                    m.insert(key.clone(), value.clone());
                } else {
                    let _ = m.remove(&key);
                }
            });
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }
}

fn new_random_array(n: usize) -> Inputs {
    let n = n as Key;
    let mut inputs: Vec<_> = (0..n).zip(0..n).collect();
    inputs.shuffle(&mut thread_rng());
    inputs
}

fn new_short_benchmark() -> Criterion {
    Criterion::default()
        .measurement_time(Duration::from_secs(10))
        .nresamples(1000)
        .sample_size(10)
}

criterion_group!(
    name = benches;
    config = new_short_benchmark();
    targets = random_operations_benchmark,
);

criterion_main!(benches);
