use std::collections::HashMap;

#[derive(Clone)]
pub struct TwoDimHashMap<T> {
    pub map: HashMap<usize, HashMap<usize, T>>,
}

impl<T> TwoDimHashMap<T> {
    pub fn get(&self, coords: (usize, usize)) -> Option<&T> {
        self.map
            .get(&coords.0)
            .and_then(|inner| inner.get(&coords.1))
    }
}

impl<T> From<HashMap<usize, HashMap<usize, T>>> for TwoDimHashMap<T> {
    fn from(value: HashMap<usize, HashMap<usize, T>>) -> Self {
        TwoDimHashMap { map: value }
    }
}
