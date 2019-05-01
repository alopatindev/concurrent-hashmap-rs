use num::Integer;
use num_traits::cast::NumCast;
use num_traits::Signed;
use std::cmp::max;
use std::fmt::Debug;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::thread;

pub const MIN_CAPACITY: usize = 1024;
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

    fn capacity(&self) -> usize {
        self.lock_table_reader().len()
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

    pub fn capacity(&self) -> usize {
        self.hash_table.capacity()
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
