use crate::hashtable::{Entry, HashTable, TableWriter, MIN_CAPACITY};
use num::Integer;
use num_traits::cast::NumCast;
use num_traits::Signed;

const MAX_LOAD_FACTOR: f64 = 0.5;

pub struct HashMap<K, V>
where
    K: Integer + Signed + NumCast + Clone + Send + Sync,
    V: PartialEq + Clone + Send + Sync,
{
    hash_table: HashTable<K, V>,
}

impl<K, V> HashMap<K, V>
where
    K: Integer + Signed + NumCast + Clone + Send + Sync,
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
        let capacity = self.hash_table.capacity();
        let load_factor = (size as f64) / (capacity as f64);
        if load_factor > MAX_LOAD_FACTOR {
            self.resize_table(capacity * 2);
        }
    }

    fn resize_table(&self, capacity: usize) {
        if capacity >= MIN_CAPACITY && self.hash_table.begin_resizing() {
            let new_hash_table = self.rebuild_hash_table(capacity);
            self.update_and_replace_hash_table(new_hash_table);
            self.hash_table.end_resizing();
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
        let new_entries: Vec<_> = new_hash_table.entries();
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
