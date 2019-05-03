use num::Integer;
use num_traits::cast::NumCast;
use num_traits::Signed;
use parking_lot::{Mutex, MutexGuard};
use std::cmp::max;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::thread;

pub const MIN_CAPACITY: usize = 1024;

pub enum Entry<K, V> {
    Vacant,
    Occupied { key: K, value: V },
    DeferredOccupied { key: K, value: V },
    Removed,
    DeferredRemoved { key: K },
}

pub type BoxedEntry<K, V> = Box<Entry<K, V>>;
pub type LockedEntry<K, V> = Mutex<BoxedEntry<K, V>>;
pub type Entries<K, V> = Vec<LockedEntry<K, V>>;

pub type TableReader<'a, K, V> = RwLockReadGuard<'a, Entries<K, V>>;
pub type TableWriter<'a, K, V> = RwLockWriteGuard<'a, Entries<K, V>>;

pub struct HashTable<K, V> {
    entries: RwLock<Entries<K, V>>,
    size: AtomicUsize,
    is_resizing: AtomicBool,
}

impl<K, V> HashTable<K, V>
where
    K: Integer + Signed + NumCast + PartialEq + Clone + Send + Sync,
    V: PartialEq + Clone + Send + Sync,
{
    const PRIME_NUMBERS: [u64; 5] = [53, 97, 193, 389, 9223372036854775807];

    pub fn new() -> Self {
        Self::with_capacity(MIN_CAPACITY)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let capacity = max(capacity, MIN_CAPACITY);

        let mut entries = Vec::with_capacity(capacity);
        entries.resize_with(capacity, || Mutex::new(Box::new(Entry::Vacant)));

        HashTable {
            entries: RwLock::new(entries),
            size: AtomicUsize::new(0),
            is_resizing: AtomicBool::new(false),
        }
    }

    pub fn len(&self) -> usize {
        self.size.load(Ordering::SeqCst)
    }

    pub fn capacity(&self) -> usize {
        self.lock_table_reader().len()
    }

    pub fn get(&self, key: &K) -> Option<V> {
        let mut capacity = std::usize::MAX;
        let mut attempt = 0;
        while attempt < capacity {
            {
                let table_reader = self.lock_table_reader();
                if Self::update_capacity_and_check_if_resized(&mut capacity, &table_reader) {
                    attempt = 0;
                    continue;
                }

                let boxed_entry = Self::lock_entry(&key, attempt, capacity, &table_reader);
                match boxed_entry.as_ref() {
                    Entry::Occupied { key: k, value: v } if *k == *key => {
                        return Some(v.clone());
                    }
                    Entry::Vacant => break,
                    Entry::DeferredRemoved { key: k } if *k == *key => break,
                    Entry::DeferredOccupied { key: k, value: _ } if *k == *key => break,
                    _ => (),
                }
            }

            self.yield_if_resizing();
            attempt += 1;
        }

        None
    }

    pub fn insert(&self, key: K, value: V) {
        let mut attempt = 0;
        let mut capacity = std::usize::MAX;
        loop {
            {
                let table_reader = self.lock_table_reader();
                if Self::update_capacity_and_check_if_resized(&mut capacity, &table_reader)
                    || attempt >= capacity
                {
                    attempt = 0;
                    continue;
                }

                let mut boxed_entry = Self::lock_entry(&key, attempt, capacity, &table_reader);
                match boxed_entry.as_ref() {
                    Entry::Vacant => {
                        *boxed_entry = self.new_occupied_entry(key, value);
                        self.size.fetch_add(1, Ordering::SeqCst);
                        break;
                    }
                    Entry::Occupied { key: k, value: _ }
                    | Entry::DeferredOccupied { key: k, value: _ }
                        if *k == key =>
                    {
                        *boxed_entry = self.new_occupied_entry(key, value);
                        break;
                    }
                    _ => (),
                }
            }

            self.yield_if_resizing();
            attempt += 1;
        }
    }

    pub fn remove(&self, key: &K) -> Option<V> {
        let mut attempt = 0;
        let mut capacity = std::usize::MAX;
        while attempt < capacity {
            {
                let table_reader = self.lock_table_reader();
                if Self::update_capacity_and_check_if_resized(&mut capacity, &table_reader) {
                    attempt = 0;
                    continue;
                }

                let mut boxed_entry = Self::lock_entry(&key, attempt, capacity, &table_reader);
                match boxed_entry.as_ref() {
                    Entry::Occupied { key: k, value: v }
                    | Entry::DeferredOccupied { key: k, value: v }
                        if *k == *key =>
                    {
                        let new_entry = self.new_removed_entry(key.clone());
                        let v = v.clone();
                        *boxed_entry = new_entry;
                        self.size.fetch_sub(1, Ordering::SeqCst);
                        return Some(v);
                    }
                    Entry::Vacant => break,
                    Entry::Removed => (),
                    Entry::DeferredRemoved { key: k } if *k == *key => break,
                    _ => (),
                }
            }

            self.yield_if_resizing();
            attempt += 1;
        }

        None
    }

    pub fn lock_table_reader(&self) -> TableReader<K, V> {
        self.entries.read().unwrap()
    }

    pub fn lock_table_writer(&self) -> TableWriter<K, V> {
        self.entries.write().unwrap()
    }

    pub fn entries(self) -> Entries<K, V> {
        self.entries.into_inner().unwrap()
    }

    pub fn begin_resizing(&self) -> bool {
        let failed = self
            .is_resizing
            .compare_and_swap(false, true, Ordering::SeqCst);
        !failed
    }

    pub fn end_resizing(&self) {
        self.is_resizing.store(false, Ordering::SeqCst);
    }

    fn update_capacity_and_check_if_resized<'a>(
        capacity: &mut usize,
        table_reader: &TableReader<'a, K, V>,
    ) -> bool {
        let new_capacity = table_reader.len();
        let is_capacity_uninitialized = *capacity == std::usize::MAX;
        if is_capacity_uninitialized {
            *capacity = new_capacity;
        }

        if *capacity != new_capacity {
            *capacity = new_capacity;
            return true;
        }

        return false;
    }

    fn yield_if_resizing(&self) {
        if self.is_resizing() {
            thread::yield_now();
        }
    }

    pub fn is_resizing(&self) -> bool {
        self.is_resizing.load(Ordering::SeqCst)
    }

    fn new_occupied_entry(&self, key: K, value: V) -> BoxedEntry<K, V> {
        let entry = if self.is_resizing() {
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
        let entry = if self.is_resizing() {
            Entry::DeferredRemoved { key: key.clone() }
        } else {
            Entry::Removed
        };

        Box::new(entry)
    }

    fn lock_entry<'a>(
        key: &K,
        attempt: usize,
        capacity: usize,
        table_reader: &'a TableReader<'a, K, V>,
    ) -> MutexGuard<'a, BoxedEntry<K, V>> {
        let index = Self::hash(&key, attempt, capacity);
        table_reader[index].lock()
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
}
