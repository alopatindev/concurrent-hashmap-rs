#[macro_use]
extern crate criterion;
#[macro_use]
extern crate lazy_static;

use concurrent_hashmap::hashmap::HashMap;
use criterion::{black_box, Criterion};
use rand::seq::SliceRandom;
use rand::thread_rng;
use std::sync::Arc;
use std::thread;

type Key = i32;
type Inputs = Vec<Key>;

const OPERATIONS_NUM: usize = 10_000;

lazy_static! {
    static ref INPUTS: Inputs = new_random_vec(OPERATIONS_NUM);
}

fn random_operations_benchmark(c: &mut Criterion) {
    for threads_num in 1..=num_cpus::get() {
        let title = format!("{} thread(s)", threads_num);
        c.bench_function(&title, move |b| {
            b.iter(|| random_operations(black_box(threads_num)))
        });
    }
}

fn random_operations(threads_num: usize) {
    let m = Arc::new(HashMap::new());
    let mut threads = Vec::new();
    let inputs_per_thread = INPUTS.len() / threads_num;
    for i in 0..threads_num {
        let m = m.clone();
        threads.push(thread::spawn(move || {
            (0..INPUTS.len())
                .skip(i * inputs_per_thread)
                .take(inputs_per_thread)
                .map(|i| (INPUTS[i], INPUTS[i]))
                .for_each(|(key, value)| {
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

fn new_random_vec(n: usize) -> Inputs {
    let n = n as Key;
    let mut inputs: Inputs = (0..n).collect();
    inputs.shuffle(&mut thread_rng());
    inputs
}

criterion_group!(benches, random_operations_benchmark);
criterion_main!(benches);
