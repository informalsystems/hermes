use crate::traits::core::Async;

pub trait ErrorContext: Async {
    type Error: Async;
}
