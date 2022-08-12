use crate::traits::core::Async;

pub trait HasError: Async {
    type Error: Async;
}
