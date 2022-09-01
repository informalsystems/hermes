use crate::core::traits::core::Async;

pub trait Filter : Async {
    fn allow(&self) -> bool;
}

pub struct EmptyFilter;

impl Filter for EmptyFilter {
    fn allow(&self) -> bool {
        true
    }
}