use std::collections::{btree_map, BTreeMap};

#[derive(Clone, Debug)]
pub struct TwoDimMap<T> {
    pub map: BTreeMap<usize, BTreeMap<usize, T>>,
}

impl<T> Default for TwoDimMap<T> {
    fn default() -> Self {
        TwoDimMap {
            map: BTreeMap::new(),
        }
    }
}

impl<T> TwoDimMap<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn get(&self, (x, y): (usize, usize)) -> Option<&T> {
        self.map.get(&x).and_then(|inner| inner.get(&y))
    }

    pub fn insert(&mut self, (x, y): (usize, usize), value: T) -> Option<T> {
        if let Some(existing_values) = self.map.get_mut(&x) {
            existing_values.insert(y, value)
        } else {
            let mut new_values = BTreeMap::new();
            new_values.insert(y, value);
            self.map.insert(x, new_values);
            None
        }
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            outer_iter: self.map.iter(),
            inner_iter: None,
            outer_key: 0,
        }
    }
}

pub struct Iter<'a, T> {
    outer_iter: btree_map::Iter<'a, usize, BTreeMap<usize, T>>,
    inner_iter: Option<btree_map::Iter<'a, usize, T>>,
    outer_key: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (usize, usize, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(inner_iter) = &mut self.inner_iter {
                if let Some((inner_key, inner_value)) = inner_iter.next() {
                    return Some((self.outer_key, *inner_key, inner_value));
                }
            }

            if let Some((outer_key, inner_map)) = self.outer_iter.next() {
                self.outer_key = *outer_key;
                self.inner_iter = Some(inner_map.iter());
            } else {
                return None;
            }
        }
    }
}

impl<T> From<BTreeMap<usize, BTreeMap<usize, T>>> for TwoDimMap<T> {
    fn from(map: BTreeMap<usize, BTreeMap<usize, T>>) -> Self {
        Self { map }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;

    #[test]
    fn test_two_dim_hash_map_iterator() {
        let mut outer_hashmap = BTreeMap::new();
        let mut inner_hashmap1 = BTreeMap::new();
        let mut inner_hashmap2 = BTreeMap::new();
        let mut inner_hashmap3 = BTreeMap::new();

        inner_hashmap1.insert(1, "a");

        inner_hashmap2.insert(2, "c");
        inner_hashmap2.insert(0, "b");

        inner_hashmap3.insert(1, "d");

        outer_hashmap.insert(0, inner_hashmap1);
        outer_hashmap.insert(1, inner_hashmap2);
        outer_hashmap.insert(2, inner_hashmap3);

        let two_dim_hash_map = TwoDimMap::from(outer_hashmap);
        let mut two_dim_hash_map_iter = two_dim_hash_map.iter();

        assert_eq!(two_dim_hash_map_iter.next(), Some((0, 1, &"a")));

        assert_eq!(two_dim_hash_map_iter.next(), Some((1, 0, &"b")));
        assert_eq!(two_dim_hash_map_iter.next(), Some((1, 2, &"c")));

        assert_eq!(two_dim_hash_map_iter.next(), Some((2, 1, &"d")));

        assert_eq!(two_dim_hash_map_iter.next(), None);
    }
}
