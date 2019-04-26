use num::Integer;
use num_traits::cast::NumCast;
use num_traits::Signed;
use std::cmp::max;
use std::fmt::Debug;
use std::ops::Index;

const MIN_CAPACITY: usize = 1024;

#[derive(Clone, Debug)]
enum Entry<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug,
    V: Clone,
{
    Vacant,
    Occupied { key: K, value: V },
    Removed,
}

struct HashMap<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug,
    V: Clone,
{
    table: Vec<Entry<K, V>>,
    size: usize,
}

impl<K, V> HashMap<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug,
    V: Clone,
{
    const PRIME_NUMBERS: [usize; 4] = [53, 97, 193, 389];
    const BIG_PRIME: usize = 9223372036854775807;

    pub fn new() -> Self {
        Self::with_capacity(MIN_CAPACITY)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let capacity = max(capacity, MIN_CAPACITY);
        HashMap {
            table: vec![Entry::Vacant; capacity],
            size: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn capacity(&self) -> usize {
        self.table.len()
    }

    pub fn contains_key(&self, key: &K) -> bool {
        for attempt in 0..self.capacity() {
            let h = self.hash(&key, attempt);
            match &self.table[h] {
                Entry::Vacant => return false,
                Entry::Occupied { key: k, value: _ } => {
                    if k == key {
                        return true;
                    }
                }
                Entry::Removed => (),
            }
        }

        false
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.maybe_increase_table();

        for attempt in 0..self.capacity() {
            let h = self.hash(&key, attempt);
            match &self.table[h] {
                Entry::Vacant | Entry::Removed => {
                    self.table[h] = Entry::Occupied {
                        key: key,
                        value: value,
                    };
                    self.size += 1;
                    break;
                }
                Entry::Occupied { key: k, value: _ } => {
                    if *k == key {
                        self.table[h] = Entry::Occupied {
                            key: key,
                            value: value,
                        };
                        break;
                    }
                }
            }
        }
    }

    pub fn remove(&mut self, key: &K) {
        for attempt in 0..self.capacity() {
            let h = self.hash(&key, attempt);
            match &self.table[h] {
                Entry::Occupied { key: k, value: _ } => {
                    if k == key {
                        self.table[h] = Entry::Removed;
                        self.size -= 1;
                        break;
                    }
                }
                Entry::Vacant | Entry::Removed => (),
            }
        }

        self.maybe_shrink_table();
    }

    fn hash(&self, key: &K, attempt: usize) -> usize {
        let h1 = Self::universal_hash(key, &Self::PRIME_NUMBERS[0..2]);
        let h2 = Self::universal_hash(key, &Self::PRIME_NUMBERS[2..4]);
        (h1 + attempt * h2) % self.capacity()
    }

    fn universal_hash(key: &K, a: &[usize]) -> usize {
        let key: usize = key.abs().to_usize().unwrap();
        ((a[0] * key + a[1]) % Self::BIG_PRIME)
    }

    fn maybe_increase_table(&mut self) {
        if self.size + 1 > self.capacity() {
            self.resize_table(self.capacity() * 2)
        }
    }

    fn maybe_shrink_table(&mut self) {
        if self.capacity() / 2 == self.size {
            self.resize_table(self.capacity() / 2)
        }
    }

    fn resize_table(&mut self, capacity: usize) {
        let items = self.table.iter().filter_map(|item| match item {
            Entry::Occupied { key, value } => Some((key, value)),
            _ => None,
        });

        let mut new_hashmap = Self::with_capacity(capacity);
        for (key, value) in items {
            new_hashmap.insert(key.clone(), value.clone());
        }

        self.table = new_hashmap.table;
    }
}

impl<K, V> Index<&K> for HashMap<K, V>
where
    K: Integer + Signed + NumCast + Clone + Debug,
    V: Clone,
{
    type Output = V;

    fn index(&self, key: &K) -> &Self::Output {
        for attempt in 0..self.capacity() {
            let h = self.hash(&key, attempt);
            match &self.table[h] {
                Entry::Occupied { key: k, value: v } => {
                    if k == key {
                        return v;
                    }
                }
                Entry::Vacant | Entry::Removed => (),
            }
        }

        panic!("no entry found for key")
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
    use std::collections::HashMap as StdHashMap;

    #[test]
    fn test_empty() {
        assert!(HashMap::<i32, i32>::new().is_empty());
    }

    #[test]
    fn test_insert() {
        let mut m = HashMap::new();
        assert!(m.is_empty());

        assert!(!m.contains_key(&1));
        m.insert(1, 1);
        assert!(m.contains_key(&1));
        assert_eq!(m.len(), 1);
        assert_eq!(m[&1], 1);

        m.insert(1, 2);
        assert!(m.contains_key(&1));
        assert_eq!(m.len(), 1);
        assert_eq!(m[&1], 2);

        assert!(!m.contains_key(&3));
        m.insert(3, 4);
        assert_eq!(m.len(), 2);
        assert!(m.contains_key(&3));
        assert_eq!(m[&3], 4);

        assert!(!m.contains_key(&-5));
        m.insert(-5, 6);
        assert_eq!(m.len(), 3);
        assert!(m.contains_key(&-5));
        assert_eq!(m[&-5], 6);

        assert!(!m.contains_key(&5));
        m.insert(5, 7);
        assert_eq!(m.len(), 4);
        assert!(m.contains_key(&5));
        assert_eq!(m[&5], 7);
    }

    #[test]
    fn test_remove() {
        let mut m = HashMap::new();
        m.insert(1, 2);
        m.insert(3, 4);

        m.remove(&1);
        assert!(!m.contains_key(&1));
        assert!(m.contains_key(&3));
        assert_eq!(m.len(), 1);

        m.remove(&3);
        assert!(m.is_empty());
        assert!(!m.contains_key(&3));

        m.insert(1, 5);
        assert_eq!(m.len(), 1);
        assert!(m.contains_key(&1));
        assert_eq!(m[&1], 5);
    }

    #[test]
    fn test_resize_table() {
        let mut m = HashMap::new();
        let last_key = (MIN_CAPACITY * 5) as i64;
        for i in 0..last_key {
            m.insert(i, i);
        }
        let capacity_after_insert = m.capacity();
        assert!(capacity_after_insert > MIN_CAPACITY);

        for i in 0..last_key {
            m.remove(&i);
        }
        assert!(m.capacity() < capacity_after_insert);
    }

    #[quickcheck]
    fn test_random_insert(inputs: Vec<(i32, i64)>) -> bool {
        let mut m = HashMap::new();
        let mut s = StdHashMap::new();
        let mut result = true;

        for (key, value) in inputs {
            result &= m.contains_key(&key) == s.contains_key(&key);
            m.insert(key, value);
            s.insert(key, value);
            result &= m.contains_key(&key) == s.contains_key(&key);
            result &= m[&key] == s[&key];
        }

        result
    }
}
