use num::Integer;
use num_traits::cast::NumCast;
use num_traits::Signed;
use std::cmp::max;
use std::fmt::Debug;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::thread;

const MIN_CAPACITY: usize = 1024;
const MAX_LOAD_FACTOR: f64 = 0.5;

#[derive(Clone, Debug, PartialEq)]
enum Entry<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug + Send + Sync,
    V: PartialEq + Clone + Send + Sync,
{
    Vacant,
    Occupied { key: K, value: V },
    DeferredOccupied { key: K, value: V },
    Removed,
    DeferredRemoved { key: K },
}

type BoxedEntry<K, V> = Box<Entry<K, V>>;
type LockedEntry<K, V> = Mutex<BoxedEntry<K, V>>;
type Entries<K, V> = Vec<LockedEntry<K, V>>;

type TableReader<'a, K, V> = RwLockReadGuard<'a, Entries<K, V>>;
type TableWriter<'a, K, V> = RwLockWriteGuard<'a, Entries<K, V>>;

struct HashTable<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug + Send + Sync,
    V: PartialEq + Clone + Send + Sync,
{
    entries: RwLock<Entries<K, V>>,
    size: AtomicUsize,
    is_resizing: AtomicBool,
}

pub struct HashMap<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug + Send + Sync,
    V: PartialEq + Clone + Send + Sync,
{
    hash_table: HashTable<K, V>,
}

impl<K, V> HashTable<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug + Send + Sync,
    V: PartialEq + Clone + Send + Sync,
{
    const PRIME_NUMBERS: [u64; 5] = [53, 97, 193, 389, 9223372036854775807];

    fn new() -> Self {
        Self::with_capacity(MIN_CAPACITY)
    }

    fn with_capacity(capacity: usize) -> Self {
        let capacity = max(capacity, MIN_CAPACITY);

        let mut entries = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            let lock = Mutex::new(Box::new(Entry::Vacant));
            entries.push(lock);
        }

        HashTable {
            entries: RwLock::new(entries),
            size: AtomicUsize::new(0),
            is_resizing: AtomicBool::new(false),
        }
    }

    fn len(&self) -> usize {
        self.size.load(Ordering::SeqCst)
    }

    fn get(&self, key: &K) -> Option<V> {
        let mut capacity = std::usize::MAX;
        let mut attempt = 0;
        while attempt < capacity {
            let table_reader = self.lock_table_reader();
            let new_capacity = table_reader.len();
            if capacity == std::usize::MAX {
                capacity = new_capacity;
            }

            let is_resized = capacity != new_capacity;
            if is_resized {
                attempt = 0;
                capacity = new_capacity;
                thread::yield_now();
                continue;
            }

            let index = Self::hash(&key, attempt, capacity);
            let entry = table_reader[index].lock().unwrap();
            match entry.as_ref() {
                Entry::Occupied {
                    key: old_key,
                    value: old_value,
                } => {
                    if *old_key == *key {
                        return Some(old_value.clone());
                    }
                }
                Entry::Vacant => break,
                Entry::Removed => (),
                Entry::DeferredRemoved { key: old_key } => {
                    if *old_key == *key {
                        break;
                    }
                }
                Entry::DeferredOccupied {
                    key: old_key,
                    value: _,
                } => {
                    if *old_key == *key {
                        break;
                    }
                }
            }

            if self.is_resizing.load(Ordering::SeqCst) {
                thread::yield_now();
            }

            attempt += 1;
        }

        None
    }

    fn insert(&self, key: K, value: V) {
        let mut attempt = 0;
        let mut capacity = std::usize::MAX;
        loop {
            {
                let table_reader = self.lock_table_reader();
                let new_capacity = table_reader.len();
                if capacity == std::usize::MAX {
                    capacity = new_capacity;
                }

                let is_resized = capacity != new_capacity;
                if is_resized || attempt >= capacity {
                    capacity = new_capacity;
                    attempt = 0;
                    thread::yield_now();
                    continue;
                }

                let index = Self::hash(&key, attempt, capacity);
                let mut entry = table_reader[index].lock().unwrap();
                match entry.as_ref() {
                    Entry::Vacant => {
                        *entry = self.new_occupied_entry(key, value);
                        self.size.fetch_add(1, Ordering::SeqCst);
                        break;
                    }
                    Entry::Occupied {
                        key: old_key,
                        value: _,
                    }
                    | Entry::DeferredOccupied {
                        key: old_key,
                        value: _,
                    } => {
                        if *old_key == key {
                            *entry = self.new_occupied_entry(key, value);
                            break;
                        }
                    }
                    Entry::Removed | Entry::DeferredRemoved { key: _ } => (),
                }
            }

            if self.is_resizing.load(Ordering::SeqCst) {
                thread::yield_now();
            }

            attempt += 1;
        }
    }

    fn remove(&self, key: &K) -> Option<V> {
        let mut attempt = 0;
        let mut capacity = std::usize::MAX;
        while attempt < capacity {
            {
                let table_reader = self.lock_table_reader();
                let new_capacity = table_reader.len();
                if capacity == std::usize::MAX {
                    capacity = new_capacity;
                }

                if capacity != new_capacity {
                    capacity = new_capacity;
                    attempt = 0;
                    thread::yield_now();
                    continue;
                }

                let index = Self::hash(&key, attempt, capacity);
                let mut entry = table_reader[index].lock().unwrap();
                match entry.as_ref() {
                    Entry::Occupied {
                        key: old_key,
                        value: old_value,
                    }
                    | Entry::DeferredOccupied {
                        key: old_key,
                        value: old_value,
                    } => {
                        if *old_key == *key {
                            let new_entry = self.new_removed_entry(key.clone());
                            let old_value = old_value.clone();
                            *entry = new_entry;
                            self.size.fetch_sub(1, Ordering::SeqCst);
                            return Some(old_value);
                        }
                    }
                    Entry::Vacant => break,
                    Entry::Removed => (),
                    Entry::DeferredRemoved { key: old_key } => {
                        if *old_key == *key {
                            break;
                        }
                    }
                }
            }

            if self.is_resizing.load(Ordering::SeqCst) {
                thread::yield_now();
            }

            attempt += 1;
        }

        None
    }

    fn new_occupied_entry(&self, key: K, value: V) -> BoxedEntry<K, V> {
        let entry = if self.is_resizing.load(Ordering::SeqCst) {
            Entry::DeferredOccupied {
                key: key,
                value: value,
            }
        } else {
            Entry::Occupied {
                key: key,
                value: value,
            }
        };
        Box::new(entry)
    }

    fn new_removed_entry(&self, key: K) -> BoxedEntry<K, V> {
        let entry = if self.is_resizing.load(Ordering::SeqCst) {
            Entry::DeferredRemoved { key: key.clone() }
        } else {
            Entry::Removed
        };
        Box::new(entry)
    }

    fn hash(key: &K, attempt: usize, capacity: usize) -> usize {
        let attempt = attempt as u64;
        let key: u64 = key.abs().to_u64().unwrap();
        let universal_hash = |a: &[u64]| (a[0] * key + a[1]) % Self::PRIME_NUMBERS[4];

        let h1 = universal_hash(&Self::PRIME_NUMBERS[0..2]);
        let h2 = universal_hash(&Self::PRIME_NUMBERS[2..4]);

        let value = h1 + attempt * h2;
        (value as usize) % capacity
    }

    fn lock_table_reader(&self) -> TableReader<K, V> {
        self.entries.read().unwrap()
    }

    fn lock_table_writer(&self) -> TableWriter<K, V> {
        self.entries.write().unwrap()
    }
}

impl<K, V> HashMap<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug + Send + Sync,
    V: PartialEq + Clone + Send + Sync,
{
    pub fn new() -> Self {
        HashMap {
            hash_table: HashTable::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.hash_table.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    pub fn get(&self, key: &K) -> Option<V> {
        self.hash_table.get(key)
    }

    pub fn insert(&self, key: K, value: V) {
        self.maybe_increase_table();
        self.hash_table.insert(key, value);
    }

    pub fn remove(&self, key: &K) -> Option<V> {
        self.hash_table.remove(key)
    }

    fn maybe_increase_table(&self) {
        let size = self.hash_table.len();
        let capacity = {
            let table_reader = self.hash_table.lock_table_reader();
            table_reader.len()
        };

        let load_factor = (size as f64) / (capacity as f64);
        if load_factor > MAX_LOAD_FACTOR {
            self.resize_table(capacity * 2);
        }
    }

    #[rustfmt::skip]
    fn resize_table(&self, capacity: usize) {
        if capacity >= MIN_CAPACITY && !self.hash_table.is_resizing.compare_and_swap(
            false,
            true,
            Ordering::SeqCst
        ) {
            let new_hash_table = self.rebuild_hash_table(capacity);
            self.update_and_replace_hash_table(new_hash_table);
            self.hash_table.is_resizing.store(false, Ordering::SeqCst);
        }
    }

    fn rebuild_hash_table(&self, capacity: usize) -> HashTable<K, V> {
        let entries: Vec<_> = {
            let table_reader = self.hash_table.lock_table_reader();
            table_reader
                .iter()
                .filter_map(|item| match *item.lock().unwrap().clone() {
                    Entry::Occupied { key, value } => Some((key, value)),
                    _ => None,
                })
                .collect()
        };

        let new_hash_table = HashTable::with_capacity(capacity);

        entries
            .into_iter()
            .for_each(|(key, value)| new_hash_table.insert(key, value));

        new_hash_table
    }

    fn update_and_replace_hash_table(&self, mut new_hash_table: HashTable<K, V>) {
        let table_writer = self.hash_table.lock_table_writer();
        let mut table_writer = Self::process_deferred_entries(table_writer, &mut new_hash_table);
        let new_entries: Vec<_> = new_hash_table.entries.into_inner().unwrap();
        *table_writer = new_entries;
    }

    fn process_deferred_entries<'a>(
        table_writer: TableWriter<'a, K, V>,
        new_hash_table: &mut HashTable<K, V>,
    ) -> TableWriter<'a, K, V> {
        table_writer
            .iter()
            .for_each(|item| match *item.lock().unwrap().clone() {
                Entry::DeferredOccupied { key, value } => new_hash_table.insert(key, value),
                _ => (),
            });

        table_writer
            .iter()
            .for_each(|item| match *item.lock().unwrap().clone() {
                Entry::DeferredRemoved { key } => {
                    let _ = new_hash_table.remove(&key);
                }
                _ => (),
            });

        table_writer
    }
}

#[cfg(test)]
extern crate quickcheck;

#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
mod tests {
    use super::*;
    use rand::seq::SliceRandom;
    use rand::thread_rng;
    use std::collections::HashMap as StdHashMap;
    use std::collections::HashSet as StdHashSet;
    use std::sync::Arc;

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

        let capacity_after_insert = m.hash_table.lock_table_reader().len();
        assert!(capacity_after_insert > MIN_CAPACITY);

        for i in 0..last_key {
            assert_eq!(m.get(&i), Some(i));
        }

        for i in 0..last_key {
            assert_eq!(m.remove(&i), Some(i));
        }

        let capacity_after_remove = m.hash_table.lock_table_reader().len();
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
        let m: Arc<HashMap<i32, i64>> = Arc::new(HashMap::new());
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

        let m: Arc<HashMap<i32, i64>> = Arc::new(HashMap::new());
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
                    .for_each(|(key, value)| m.insert(key.clone(), value.clone()))
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
                            result.compare_and_swap(
                                true,
                                s[&key].contains(&value),
                                Ordering::SeqCst,
                            );
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
        let m: Arc<HashMap<i32, i32>> = Arc::new(HashMap::new());
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
                    .for_each(|j| {
                        m.insert(j, j);
                    })
            }));
        }

        for thread in threads {
            thread.join().unwrap();
        }

        let capacity_after_insert = m.hash_table.lock_table_reader().len();
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
                        result.compare_and_swap(true, m.get(&j) == Some(j), Ordering::SeqCst);
                    })
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
                    })
            }));
        }

        for thread in threads {
            thread.join().unwrap();
        }

        let capacity_after_remove = m.hash_table.lock_table_reader().len();
        assert_eq!(capacity_after_remove, capacity_after_insert);
        assert!(m.is_empty());
    }

    #[test]
    fn test_deferred_removes() {
        let m: Arc<HashMap<i32, i32>> = Arc::new(HashMap::new());
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
                    .for_each(|j| {
                        m.insert(j, j);
                    })
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
                    })
            }));
        }

        for thread in threads {
            thread.join().unwrap();
        }
    }

    #[test]
    fn test_large_input() {
        let input_size: i32 = 1_000_000;
        let mut inputs: Vec<(i32, i32)> = (0..input_size).zip(0..input_size).collect();
        inputs.shuffle(&mut thread_rng());

        let m: Arc<HashMap<i32, i32>> = Arc::new(HashMap::new());
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
}
