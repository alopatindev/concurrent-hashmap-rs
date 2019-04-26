use num::Integer;
use std::ops::Index;

#[derive(Clone)]
enum Entry<K, V>
where
    K: Integer + Clone,
    V: Clone,
{
    Vacant,
    Occupied { key: K, value: V },
    Removed,
}

struct HashMap<K, V>
where
    K: Integer + Clone,
    V: Clone,
{
    table: Vec<Entry<K, V>>,
    size: usize,
}

impl<K, V> HashMap<K, V>
where
    K: Integer + Clone,
    V: Clone,
{
    pub fn new() -> Self {
        unimplemented!()
    }

    pub fn with_capacity(capacity: usize) -> Self {
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
        unimplemented!()
    }

    pub fn contains_key(&self, key: &K) -> bool {
        unimplemented!()
    }

    pub fn insert(&mut self, key: K, value: V) {
        unimplemented!()
    }

    pub fn remove(&mut self, key: &K) {
        unimplemented!()
    }
}

impl<K, V> Index<&K> for HashMap<K, V>
where
    K: Integer + Clone,
    V: Clone,
{
    type Output = V;

    fn index(&self, key: &K) -> &Self::Output {
        unimplemented!()
    }
}

#[cfg(test)]
extern crate quickcheck;

#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
mod tests {
    use super::HashMap;
    use std::collections::HashMap as StdHashMap;

    #[test]
    fn test_empty() {
        assert!(HashMap::<i32, i32>::new().is_empty());
        assert!(HashMap::<i32, i32>::with_capacity(0).is_empty())
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
        assert_eq!(m[&3], 5);
    }

    #[quickcheck]
    fn random_insert(inputs: Vec<(i32, i64)>) -> bool {
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
