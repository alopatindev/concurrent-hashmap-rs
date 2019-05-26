extern crate concurrent_hashmap;
extern crate quickcheck;
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use concurrent_hashmap::hashmap::{HashMap, MIN_CAPACITY};
use rand::seq::SliceRandom;
use rand::thread_rng;
use std::collections::HashMap as StdHashMap;
use std::collections::HashSet as StdHashSet;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

#[test]
fn test_empty() {
    assert!(HashMap::<i32, i32>::new().is_empty());
}

#[test]
fn test_insert() {
    let m = HashMap::new();
    assert!(m.is_empty());

    assert!(!m.contains_key(&1));
    m.insert(1, 1);
    assert!(m.contains_key(&1));
    assert_eq!(m.len(), 1);
    assert_eq!(m.get(&1), Some(1));

    m.insert(1, 2);
    assert!(m.contains_key(&1));
    assert_eq!(m.len(), 1);
    assert_eq!(m.get(&1), Some(2));

    assert!(!m.contains_key(&3));
    m.insert(3, 4);
    assert_eq!(m.len(), 2);
    assert!(m.contains_key(&3));
    assert_eq!(m.get(&3), Some(4));

    assert!(!m.contains_key(&-5));
    m.insert(-5, 6);
    assert_eq!(m.len(), 3);
    assert!(m.contains_key(&-5));
    assert_eq!(m.get(&-5), Some(6));

    assert!(!m.contains_key(&5));
    m.insert(5, 7);
    assert_eq!(m.len(), 4);
    assert!(m.contains_key(&5));
    assert_eq!(m.get(&5), Some(7));
}

#[test]
fn test_insert_bounds() {
    let m = HashMap::new();

    let key = std::i64::MAX;
    m.insert(key, 0);
    assert!(m.contains_key(&key));
    assert_eq!(m.get(&key), Some(0));

    let key = std::i64::MIN + 1;
    m.insert(key, 1);
    assert!(m.contains_key(&key));
    assert_eq!(m.get(&key), Some(1));
}

#[test]
fn test_remove() {
    let m = HashMap::new();
    m.insert(1, 2);
    m.insert(3, 4);

    assert_eq!(m.remove(&1), Some(2));
    assert!(!m.contains_key(&1));
    assert!(m.contains_key(&3));
    assert_eq!(m.len(), 1);

    assert_eq!(m.remove(&3), Some(4));
    assert!(m.is_empty());
    assert!(!m.contains_key(&3));

    m.insert(1, 5);
    assert_eq!(m.len(), 1);
    assert!(m.contains_key(&1));
    assert_eq!(m.get(&1), Some(5));
}

#[test]
fn test_resize_table() {
    let m = HashMap::new();

    let last_key = (MIN_CAPACITY * 100) as i64;
    for i in 0..last_key {
        m.insert(i, i);
    }

    let capacity_after_insert = m.capacity();
    assert!(capacity_after_insert > MIN_CAPACITY);

    for i in 0..last_key {
        assert_eq!(m.get(&i), Some(i));
    }

    for i in 0..last_key {
        assert_eq!(m.remove(&i), Some(i));
    }

    let capacity_after_remove = m.capacity();
    assert_eq!(capacity_after_remove, capacity_after_insert);
}

#[quickcheck]
fn test_random_insert(inputs: Vec<(i32, i64)>) -> bool {
    let m = HashMap::new();
    let mut s = StdHashMap::new();
    let mut result = true;

    for (key, value) in inputs {
        result &= m.contains_key(&key) == s.contains_key(&key);
        m.insert(key, value);
        s.insert(key, value);
        result &= m.contains_key(&key) == s.contains_key(&key);
        result &= m.get(&key).unwrap() == s[&key];
    }

    result &= m.len() == s.len();
    result
}

#[quickcheck]
fn test_concurrent_insert(inputs: Vec<(i32, i64)>) -> bool {
    let result = Arc::new(AtomicBool::new(true));
    let threads_num = num_cpus::get();
    let inputs_per_thread = inputs.len() / threads_num;

    let mut s: StdHashMap<i32, StdHashSet<i64>> = StdHashMap::new();
    for i in 0..threads_num {
        inputs
            .iter()
            .skip(i * inputs_per_thread)
            .take(inputs_per_thread)
            .for_each(|(key, value)| {
                if !s.contains_key(key) {
                    s.insert(key.clone(), StdHashSet::new());
                }
                s.get_mut(key).unwrap().insert(value.clone());
            });
    }

    let inputs = Arc::new(inputs);
    let m = Arc::new(HashMap::new());
    let mut threads = Vec::new();
    for i in 0..threads_num {
        let m = m.clone();
        let inputs = inputs.clone();
        threads.push(thread::spawn(move || {
            inputs
                .iter()
                .skip(i * inputs_per_thread)
                .take(inputs_per_thread)
                .for_each(|(key, value)| m.insert(key.clone(), value.clone()));
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }

    let s = Arc::new(s);
    let mut threads = Vec::new();
    for i in 0..threads_num {
        let result = result.clone();
        let m = m.clone();
        let s = s.clone();
        threads.push(thread::spawn(move || {
            s.keys()
                .skip(i * inputs_per_thread)
                .take(inputs_per_thread)
                .for_each(|key| {
                    result.compare_and_swap(true, m.contains_key(&key), Ordering::SeqCst);
                    result.compare_and_swap(
                        true,
                        s[&key].contains(&m.get(&key).unwrap()),
                        Ordering::SeqCst,
                    );
                });
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }

    result.compare_and_swap(true, s.len() == m.len(), Ordering::SeqCst);
    result.load(Ordering::SeqCst)
}

#[quickcheck]
fn test_concurrent_remove(inputs: Vec<(i32, i64)>) -> bool {
    let result = Arc::new(AtomicBool::new(true));
    let threads_num = num_cpus::get();
    let inputs_per_thread = inputs.len() / threads_num;

    let mut s: StdHashMap<i32, StdHashSet<i64>> = StdHashMap::new();
    for i in 0..threads_num {
        inputs
            .iter()
            .skip(i * inputs_per_thread)
            .take(inputs_per_thread)
            .for_each(|(key, value)| {
                if !s.contains_key(key) {
                    s.insert(key.clone(), StdHashSet::new());
                }
                s.get_mut(key).unwrap().insert(value.clone());
            });
    }

    let m = Arc::new(HashMap::new());
    let inputs = Arc::new(inputs);
    let mut threads = Vec::new();
    for i in 0..threads_num {
        let m = m.clone();
        let inputs = inputs.clone();
        threads.push(thread::spawn(move || {
            inputs
                .iter()
                .skip(i * inputs_per_thread)
                .take(inputs_per_thread)
                .for_each(|(key, value)| m.insert(key.clone(), value.clone()));
        }))
    }

    for thread in threads {
        thread.join().unwrap();
    }

    let s = Arc::new(s);
    let mut threads = Vec::new();
    for i in 0..threads_num {
        let result = result.clone();
        let m = m.clone();
        let s = s.clone();
        let inputs = inputs.clone();
        threads.push(thread::spawn(move || {
            inputs
                .iter()
                .skip(i * inputs_per_thread)
                .take(inputs_per_thread)
                .for_each(|(key, _)| match m.remove(&key) {
                    Some(value) => {
                        result.compare_and_swap(true, s[&key].contains(&value), Ordering::SeqCst);
                    }
                    None => (),
                });
        }))
    }

    for thread in threads {
        thread.join().unwrap();
    }

    let mut threads = Vec::new();
    for i in 0..threads_num {
        let result = result.clone();
        let m = m.clone();
        let inputs = inputs.clone();
        threads.push(thread::spawn(move || {
            inputs
                .iter()
                .skip(i * inputs_per_thread)
                .take(inputs_per_thread)
                .for_each(|(key, _value)| {
                    result.compare_and_swap(true, !m.contains_key(&key), Ordering::SeqCst);
                })
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }

    result.compare_and_swap(true, m.is_empty(), Ordering::SeqCst);
    result.load(Ordering::SeqCst)
}

#[test]
fn test_concurrent_resize_table() {
    let m = Arc::new(HashMap::new());
    let last_key = (MIN_CAPACITY * 100) as i32;
    let threads_num = num_cpus::get() as i32;
    let inputs_per_thread = last_key / threads_num;

    let mut threads = Vec::new();
    for i in 0..threads_num {
        let m = m.clone();
        threads.push(thread::spawn(move || {
            (0..last_key)
                .skip((i * inputs_per_thread) as usize)
                .take(inputs_per_thread as usize)
                .for_each(|j| m.insert(j, j));
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }

    let capacity_after_insert = m.capacity();
    assert!(capacity_after_insert > MIN_CAPACITY);

    let result = Arc::new(AtomicBool::new(true));
    let mut threads = Vec::new();
    for i in 0..threads_num {
        let m = m.clone();
        let result = result.clone();
        threads.push(thread::spawn(move || {
            (0..last_key)
                .skip((i * inputs_per_thread) as usize)
                .take(inputs_per_thread as usize)
                .for_each(|j| {
                    let _ = result.compare_and_swap(true, m.get(&j) == Some(j), Ordering::SeqCst);
                });
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }

    assert!(result.load(Ordering::SeqCst));

    let mut threads = Vec::new();
    for i in 0..threads_num {
        let m = m.clone();
        threads.push(thread::spawn(move || {
            (0..last_key)
                .skip((i * inputs_per_thread) as usize)
                .take(inputs_per_thread as usize)
                .for_each(|j| {
                    let _ = m.remove(&j);
                });
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }

    let capacity_after_remove = m.capacity();
    assert_eq!(capacity_after_remove, capacity_after_insert);
    assert!(m.is_empty());
}

#[test]
fn test_deferred_removes() {
    let m = Arc::new(HashMap::new());
    let last_key = (MIN_CAPACITY * 100) as i32;
    let threads_num = num_cpus::get() as i32;
    let inputs_per_thread = last_key / threads_num;

    let mut threads = Vec::new();
    for i in 0..threads_num {
        let m = m.clone();
        threads.push(thread::spawn(move || {
            (0..last_key)
                .skip((i * inputs_per_thread) as usize)
                .take(inputs_per_thread as usize)
                .for_each(|j| m.insert(j, j));
        }));
    }

    let mut threads = Vec::new();
    for i in 0..threads_num {
        let m = m.clone();
        threads.push(thread::spawn(move || {
            (0..last_key)
                .skip((i * inputs_per_thread) as usize)
                .take(inputs_per_thread as usize)
                .for_each(|j| {
                    let _ = m.remove(&j);
                });
        }));
    }

    for thread in threads {
        thread.join().unwrap();
    }
}

#[test]
fn test_large_input() {
    let input_size: i32 = 500_000;
    let mut inputs: Vec<_> = (0..input_size).zip(0..input_size).collect();
    inputs.shuffle(&mut thread_rng());

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
