use std::collections::HashMap;
use std::hash::Hash;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Change<K> {
    Added(K),
    Updated(K),
    Removed(K),
}

pub fn diff<'a, K, V, F>(
    prev: &'a HashMap<K, V>,
    next: &'a HashMap<K, V>,
    eq: F,
) -> Vec<Change<&'a K>>
where
    K: Hash + Eq,
    F: Fn(&'a V, &'a V) -> bool,
{
    let mut changes = Vec::new();

    for (key, value) in prev {
        if let Some(next_value) = next.get(key) {
            if !eq(value, next_value) {
                changes.push(Change::Updated(key));
            }
        } else {
            changes.push(Change::Removed(key));
        }
    }

    for key in next.keys() {
        if !prev.contains_key(key) {
            changes.push(Change::Added(key));
        }
    }

    changes
}

#[cfg(test)]
mod tests {
    use super::*;
    use Change::*;

    #[test]
    fn it_works() {
        let prev = vec![(1, 1), (2, 2), (3, 3), (4, 4)].into_iter().collect();
        let next = vec![(1, 11), (2, 2), (4, 44), (5, 5)].into_iter().collect();

        let mut diff = diff(&prev, &next, |a, b| a == b);
        diff.sort();

        assert_eq!(diff, vec![Added(&5), Updated(&1), Updated(&4), Removed(&3)]);
    }
}
