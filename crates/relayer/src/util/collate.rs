use std::{fmt, ops::Add};

use serde::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Collated<T> {
    pub start: T,
    pub end: T,
}

impl<T> Collated<T> {
    pub fn new(start: T, end: T) -> Self {
        Self { start, end }
    }
}

impl<T: fmt::Display> fmt::Display for Collated<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..={}", self.start, self.end)
    }
}

pub struct Collate<Iter, Item> {
    iter: Iter,
    current: Option<Collated<Item>>,
}

impl<Iter, Item> Collate<Iter, Item> {
    pub fn new(iter: Iter) -> Self {
        Self {
            iter,
            current: None,
        }
    }
}

impl<Iter, Item> Iterator for Collate<Iter, Item>
where
    Iter: Iterator<Item = Item>,
    Item: PartialOrd + Add<u64, Output = Item> + Copy,
{
    type Item = Collated<Item>;

    fn next(&mut self) -> Option<Self::Item> {
        for item in self.iter.by_ref() {
            if let Some(current) = self.current.take() {
                if item == current.end {
                    self.current = Some(current);
                } else if item == current.end + 1 {
                    self.current = Some(Collated::new(current.start, item));
                } else {
                    self.current = Some(Collated::new(item, item));
                    return Some(current);
                }
            } else {
                self.current = Some(Collated::new(item, item));
            }
        }

        self.current.take()
    }
}

pub fn collate<Iter, Item>(iter: Iter) -> Collate<Iter, Item>
where
    Iter: Iterator<Item = Item>,
    Item: PartialOrd,
{
    Collate::new(iter)
}

pub trait CollatedIterExt: Iterator {
    fn collated(self) -> Collate<Self, Self::Item>
    where
        Self: Sized;
}

impl<T: ?Sized> CollatedIterExt for T
where
    T: Iterator,
{
    fn collated(self) -> Collate<Self, Self::Item>
    where
        Self: Sized,
    {
        Collate::new(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let items = vec![
            1, 2, 3, 10, 10, 10, 11, 11, 20, 30, 31, 31, 32, 33, 35, 40, 40, 40, 40,
        ];

        let collated = items.into_iter().collated().collect::<Vec<_>>();

        assert_eq!(
            collated,
            vec![
                Collated::new(1, 3),
                Collated::new(10, 11),
                Collated::new(20, 20),
                Collated::new(30, 33),
                Collated::new(35, 35),
                Collated::new(40, 40),
            ]
        );
    }
}
